import Pictures.Differences

/-!
# The drawn table is `ddt`

A kernel check, kept apart from `Differences.lean` so that the picture opens quickly: row `a = 1` of the
table the picture draws agrees with the definition `ddt` in every one of its 256 cells. It takes about two
minutes, because the kernel evaluates the S-box byte by byte.
-/

namespace Pictures

open AES

theorem ddtRow_one : ∀ b : Fin 256, (ddtRow 1)[b.val]! = ddt 1 b.val.toUInt8 := by
  decide +kernel

end Pictures
