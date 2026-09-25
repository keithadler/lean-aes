#!/usr/bin/env python3
"""Ask Lean Studio about this project from the command line, through its MCP server.

Lean Studio (https://github.com/keithadler/leanstudio) is an MCP server as well as an editor:
`LeanStudio --mcp` runs its tools with no window. This is the smallest client that can call them, so the
checks the editor makes (build, Tenet's verdict, the project map, lint, the proof walkthroughs) can be run
by a script or CI exactly as the editor runs them.

    python3 tools/leanstudio.py verify
    python3 tools/leanstudio.py export_walkthrough path=AES/RoundTrip.lean output=docs/walkthroughs/RoundTrip.html
    python3 tools/leanstudio.py build verify project_map        # several tools, one server

`LEANSTUDIO` names the server command (default `leanstudio`, which the Homebrew cask puts on PATH; from
source it is `dotnet path/to/LeanStudio.dll`). Arguments are `key=value`; a value that parses as JSON is
passed as JSON. Exits non-zero if any tool reports an error.
"""
import json
import os
import shlex
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def parse(argv):
    """Split `tool k=v k=v tool …` into [(tool, {k: v})]."""
    calls = []
    for a in argv:
        if "=" in a and calls:
            k, v = a.split("=", 1)
            try:
                v = json.loads(v)
            except json.JSONDecodeError:
                pass
            calls[-1][1][k] = v
        else:
            calls.append((a, {}))
    return calls


def main() -> int:
    calls = parse(sys.argv[1:])
    if not calls:
        print(__doc__)
        return 2
    cmd = shlex.split(os.environ.get("LEANSTUDIO", "leanstudio")) + ["--mcp", "--project", ROOT]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, cwd=ROOT)

    def rpc(i, method, params):
        proc.stdin.write(json.dumps({"jsonrpc": "2.0", "id": i, "method": method, "params": params}) + "\n")
        proc.stdin.flush()
        while True:
            line = proc.stdout.readline()
            if not line:
                raise RuntimeError("the Lean Studio server exited")
            msg = json.loads(line)
            if msg.get("id") == i:
                return msg

    rpc(0, "initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                          "clientInfo": {"name": "lean-aes", "version": "1"}})
    proc.stdin.write(json.dumps({"jsonrpc": "2.0", "method": "notifications/initialized"}) + "\n")
    failed = False
    for n, (tool, args) in enumerate(calls, start=1):
        msg = rpc(n, "tools/call", {"name": tool, "arguments": args})
        result = msg.get("result") or {}
        text = "\n".join(c.get("text", "") for c in result.get("content", []))
        err = msg.get("error") or result.get("isError")
        print(f"== {tool} {json.dumps(args) if args else ''}".rstrip())
        print(text or json.dumps(msg.get("error")))
        failed |= bool(err)
    proc.stdin.close()
    proc.wait(timeout=60)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
