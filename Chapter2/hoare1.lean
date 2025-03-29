import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Chapter2.Imp

namespace Hoare1

def Assertion := Imp.State -> Prop

-- Examples
def assertion1 (x y : String): Assertion := fun st => st x ≤ st y
def assertion2 (x y : String): Assertion := fun st => st x = 3 ∨ st x ≤ st y

def assert_implies (p q : Assertion): Prop := ∀ st, p st → q st
def assert_iff (p q : Assertion): Prop := ∀ st, p st → q st ∧ q st → p st

def valid_hoare_triple (p q : Assertion) (c : Imp.Command): Prop :=
  ∀ (st₁ st₂ : Imp.State), Imp.CEval st₁ c st₂ → p st₁ → q st₂

notation p " ->> " q  => assert_implies p q
notation p " <<->> " q => assert_iff p q
notation "{" p "} " c " {" q "}" => valid_hoare_triple p q c

-- If q holds in every state, then any triple with q as its precondition is valid.
theorem hoare_post_true : ∀ (p q : Assertion) (c : Imp.Command),
  (∀ (st : Imp.State), q st) → valid_hoare_triple p q c := by
  intros p q c hq_st
  unfold valid_hoare_triple
  intros st₁ st₂ hc hp
  apply hq_st st₂

-- if p holds in no state, then any triple with p as its precondition is valid
theorem hoare_pre_false : ∀ (p q : Assertion) (c : Imp.Command),
  (∀ (st : Imp.State), ¬(p st)) → valid_hoare_triple p q c := by
  intros p q c hq_st
  unfold valid_hoare_triple
  intros st₁ st₂ hc hp
  apply hq_st st₁ at hp
  contradiction

end Hoare1
