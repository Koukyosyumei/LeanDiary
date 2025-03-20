import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Chapter2.Imp

namespace Equiv

def cequiv (c₁ c₂ : Imp.Command) : Prop :=
    ∀ (st st' : Imp.State),
    Imp.CEval c₁ st st' ↔ Imp.CEval c₂ st st'

-- Executing `skip` does not change the Imp.State
-- This directly follows from the `skip` rule
theorem skip_preserves_Imp.State:
  ∀ (st: Imp.State), Imp.CEval Imp.Command.skip st st := by
  apply Imp.CEval.skip

-- Proving a Imp.Command equivalence

-- ∀c, (skip; c) is equivalent to c
theorem skip_left:
  ∀ (c: Imp.Command), cequiv (.seq .skip c) c := by
  intro c
  -- breaking the Imp.Statement into two directions
  rw [cequiv]
  intros st st'
  constructor
  -- forward (→)
  . intro h
    -- Since `h` is a proof about a sequence evaluation, it must have been constructed using the `seq` rule.
    -- This breaks `h` down into its components.
    cases h
    -- This pattern matches the `seq` constructor, giving us:
    --     `st''`: An intermediate Imp.State after executing skip
    --     `h_skip`: A proof that `Imp.CEval Imp.Command.skip st st''`
    --     `h_c`: A proof that `Imp.CEval c st'' st'`
    case seq st'' h_skip h_c =>
        cases h_skip
        -- Matches the `skip` constructor
        case skip =>
            exact h_c
  -- backward (←)
  . intro h
    apply Imp.CEval.seq
    . apply Imp.CEval.skip
    . exact h

theorem skip_right:
    ∀ (c: Imp.Command), cequiv (.seq c .skip) c := by
    intro c
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' h_c h_skip =>
        cases h_skip
        case skip =>
            exact h_c
    . intro h
      apply Imp.CEval.seq
      . exact h
      . apply Imp.CEval.skip

theorem if_true:
    ∀ (b: Bool), ∀ (c₁ c₂ : Imp.Command), b = true → cequiv (.if_ b c₁ c₂) c₁ := by
    intros b c₁ c₂ htrue
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hc =>
        exact hc
      case if_false hfalse hc =>
        contradiction
    . intro h
      rw[htrue]
      apply Imp.CEval.if_true
      exact h

theorem if_false:
    ∀ (b: Bool), ∀ (c₁ c₂ : Imp.Command), b = false → cequiv (.if_ b c₁ c₂) c₂ := by
    intros b c₁ c₂ hfalse
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case if_true hc =>
        contradiction
      case if_false _ hc =>
        exact hc
    . intro h
      rw[hfalse]
      apply Imp.CEval.if_false
      exact b
      exact h


theorem swap_if_branches:
    ∀ (b : Bool), ∀ (c₁ c₂ : Imp.Command), cequiv (.if_ b c₁ c₂) (.if_ (¬b) c₂ c₁) := by
    intros b c₁ c₂
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases b
      case false =>
        rw[if_true]
        rw[if_false] at h
        exact h
        repeat rfl
      case true =>
        rw[if_false]
        rw[if_true] at h
        exact h
        repeat rfl
    . intro h
      cases b
      case false =>
        rw[if_false]
        rw[if_true] at h
        exact h
        repeat rfl
      case true =>
        rw[if_true]
        rw[if_false] at h
        exact h
        repeat rfl

theorem while_false:
    ∀ (c : Imp.Command), cequiv (.while false c) .skip := by
    intros c₁
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case while_false _ =>
        apply Imp.CEval.skip
    . intro h
      cases h
      case skip =>
        apply Imp.CEval.while_false

theorem seq_assoc:
    ∀ (c₁ c₂ c₃ : Imp.Command), cequiv (.seq (.seq c₁ c₂) c₃) (.seq c₁ (.seq c₂ c₃)) := by
    intros c₁ c₂ c₃
    rw[cequiv]
    intros st st'
    constructor
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hs
        case seq st1 h1 h2 =>
            apply Imp.CEval.seq
            . exact h1
            apply Imp.CEval.seq
            . exact h2
            . exact hc
    . intro h
      cases h
      case seq st'' hs hc =>
        cases hc
        case seq st1 h1 h2 =>
            apply Imp.CEval.seq
            apply Imp.CEval.seq
            .exact hs
            .exact h1
            .exact h2

lemma h_eq (st: Imp.State) (x : String) : Imp.set st x (Imp.get st x) = st := by
    funext y
    unfold Imp.set Imp.get
    by_cases h: y = x
    {
        rw[if_pos h]
        rw[h]
    }
    {
        rw[if_neg h]
    }

theorem while_true_nonterm :
  ∀ (c: Imp.Command), ∀ (st₁ st₂: Imp.State), ¬Imp.CEval (.while true c) st₁ st₂ := by
  intros c st₁ st₂ h
  generalize e : Imp.Command.while true c = c' at h
  induction h <;>
  cases e
  next ih =>
    apply ih
    rfl

theorem while_true : ∀ (c: Imp.Command), ∀ (b : Bool),
  (b = true) → cequiv (.while b c) (.while true .skip) := by
  intros c b htrue
  rw[cequiv]
  intros st₁ st₂
  constructor
  . intro h
    rw[htrue] at h
    apply while_true_nonterm at h
    contradiction
  . intro h
    apply while_true_nonterm at h
    contradiction

theorem loop_unrolling : ∀ (c: Imp.Command), ∀ (b : Bool),
  cequiv (.while b c) (.if_ b (.seq c (.while b c)) .skip) := by
  intros c b
  rw[cequiv]
  intros st₁ st₂
  constructor
  . intro h
    cases b
    case false =>

end Equiv
