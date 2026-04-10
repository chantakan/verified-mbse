import VerifiedMBSE.Core.Interpretation
import VerifiedMBSE.Behavior.Temporal

/-!
# FDIR 仕様と StateMachineComponent

FDIRSpec（安全性・検知・復旧の3要件構造体）と、
構造モデル（PartDef）と振る舞いモデル（StateMachine）を統合する
StateMachineComponent を定義する。
-/

namespace VerifiedMBSE.Behavior

open VerifiedMBSE.Core

-- ============================================================
-- §1  FDIRSpec
-- ============================================================

/-- FDIRSpec: FDIR の3要件を集約する構造体。
    この型の値を構成すること = 全 FDIR 要件の機械的検証。 -/
structure FDIRSpec
    {S D : Type} {inv : S → D → Prop}
    (sm : StateMachine S D inv)
    (isFault    : S → Prop)
    (isNominal  : S → Prop)
    (isSafe     : D → Prop) :
    Prop where
  /-- R1 安全性: □(isSafe d) -/
  safety    : Always sm (fun _ d => isSafe d)
  /-- R2 故障検知可能性: ◇(isFault s) -/
  detection : Eventually sm (fun s _ => isFault s)
  /-- R3 故障復旧可能性: □(isFault s → ◇(isNominal s')) -/
  recovery  : Leads sm (fun s _ => isFault s) (fun s _ => isNominal s)

-- ============================================================
-- §2  StateMachineComponent（構造 + 振る舞い統合）
-- ============================================================

/-- SMInvariantCompatible: 状態機械の不変条件が PartDef の不変条件を含意する。
    構造モデルと振る舞いモデルの整合性条件。 -/
def SMInvariantCompatible
    (pd  : PartDef)
    (S   : Type)
    (I   : Interpretation)
    (inv : S → I pd.baseType → Prop) : Prop :=
  ∀ (s : S) (d : I pd.baseType), inv s d → pd.invariant

/-- StateMachineComponent: PartDef に状態機械の振る舞いを付加したコンポーネント。 -/
structure StateMachineComponent
    (I   : Interpretation)
    (pd  : PartDef)
    (S   : Type)
    (inv : S → I pd.baseType → Prop) where
  /-- 整合性証明 -/
  compat : SMInvariantCompatible pd S I inv
  /-- 振る舞いを規定する状態機械 -/
  sm     : StateMachine S (I pd.baseType) inv

/-- StateMachineComponent の整合性条件。 -/
def StateMachineComponent.WellFormed
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv) : Prop :=
  smc.sm.WellFormed

/-- Phase 2/3 接続定理：到達可能な (状態, データ) から PartInstance を構成する。 -/
def StateMachineComponent.reachable_gives_instance
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv)
    {s   : S}
    {d   : I pd.baseType}
    (hr  : Reachable smc.sm s d) :
    PartInstance I pd :=
  { carrier   := d
    inv_holds := smc.compat s d hr.inv_holds }

/-- WellFormed なら PartInstance が存在する。 -/
noncomputable def StateMachineComponent.wellFormed_gives_instance
    {I   : Interpretation}
    {pd  : PartDef}
    {S   : Type}
    {inv : S → I pd.baseType → Prop}
    (smc : StateMachineComponent I pd S inv)
    (hwf : smc.WellFormed) :
    PartInstance I pd :=
  smc.reachable_gives_instance
    (Reachable.init (Classical.choose hwf) (Classical.choose_spec hwf))

end VerifiedMBSE.Behavior
