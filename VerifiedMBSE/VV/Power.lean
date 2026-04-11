/-!
# Mode-Dependent Power Consumption and Power Budget

Defines `ModePowerSpec` and `PowerBudgetOK₂`, and derives budget satisfaction
across all mode combinations from the sum of per-subsystem max power.
-/

namespace VerifiedMBSE.VV

-- ============================================================
-- §1  ModePowerSpec
-- ============================================================

/-- ModePowerSpec: mode-dependent power consumption specification. -/
structure ModePowerSpec (S : Type) where
  /-- Power consumption function per mode -/
  modePower : S → Nat
  /-- Maximum power consumption (max over all modes) -/
  maxPower : Nat
  /-- maxPower is an upper bound for all modes -/
  maxPower_bound : ∀ s : S, modePower s ≤ maxPower

-- ============================================================
-- §2  Power Budget
-- ============================================================

/-- Proposition that the combined power of two subsystems is within budget. -/
def PowerBudgetOK₂
    {S₁ S₂ : Type}
    (pw₁ : ModePowerSpec S₁) (pw₂ : ModePowerSpec S₂)
    (budget : Nat) (m₁ : S₁) (m₂ : S₂) : Prop :=
  pw₁.modePower m₁ + pw₂.modePower m₂ ≤ budget

/-- If the sum of maxPower values is within budget, then all mode combinations are within budget. -/
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
