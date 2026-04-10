/-!
# Mode-Dependent Power Consumption and Power Budget

Defines `ModePowerSpec` and `PowerBudgetOK₂`, and derives budget satisfaction
across all mode combinations from the sum of per-subsystem max power.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ModePowerSpec
-- ============================================================

/-- ModePowerSpec: モード別消費電力の仕様。 -/
structure ModePowerSpec (S : Type) where
  /-- モード別消費電力関数 -/
  modePower : S → Nat
  /-- 最大消費電力（全モードの max） -/
  maxPower : Nat
  /-- maxPower は全モードの上界 -/
  maxPower_bound : ∀ s : S, modePower s ≤ maxPower

-- ============================================================
-- §2  電力バジェット
-- ============================================================

/-- 二つのサブシステムの電力バジェットが予算内であることの命題。 -/
def PowerBudgetOK₂
    {S₁ S₂ : Type}
    (pw₁ : ModePowerSpec S₁) (pw₂ : ModePowerSpec S₂)
    (budget : Nat) (m₁ : S₁) (m₂ : S₂) : Prop :=
  pw₁.modePower m₁ + pw₂.modePower m₂ ≤ budget

/-- maxPower の和が予算内なら、全モード組み合わせで予算内。 -/
theorem powerBudget₂_from_max
    {S₁ S₂ : Type}
    (pw₁ : ModePowerSpec S₁) (pw₂ : ModePowerSpec S₂)
    (budget : Nat)
    (h : pw₁.maxPower + pw₂.maxPower ≤ budget) :
    ∀ (m₁ : S₁) (m₂ : S₂), PowerBudgetOK₂ pw₁ pw₂ budget m₁ m₂ := by
  intro m₁ m₂
  unfold PowerBudgetOK₂
  have h₁ := pw₁.maxPower_bound m₁
  have h₂ := pw₂.maxPower_bound m₂
  omega

end VerifiedMBSE.VV
