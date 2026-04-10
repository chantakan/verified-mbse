import Lake
open Lake DSL

package «verified-mbse» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- ライブラリ本体: `require verifiedMbse from git ...` で利用可能
lean_lib VerifiedMBSE where
  roots := #[`VerifiedMBSE]

-- 宇宙機ケーススタディ（ライブラリの利用例）
lean_lib Examples where
  roots := #[`Examples]
  globs := #[.submodules `Examples]

-- CLI（将来拡張）
-- @[default_target]
-- lean_exe vmcheck where
--   root := `Main
