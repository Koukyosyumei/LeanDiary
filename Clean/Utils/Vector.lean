import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.ZMod.Basic

variable {α β : Type} {n : ℕ}

def Vec (α : Type) (n: ℕ) := { l: List α // l.length = n }

instance [Repr α] {n: ℕ} : Repr (Vec α n) where
  reprPrec l _ := repr l.val

@[reducible]
def vec (l : List α): Vec α l.length := ⟨ l, rfl ⟩

namespace Vec

def len (_: Vec α n): ℕ := n

@[ext]
theorem ext (l : ℕ) (v w: Vec α l) : v.val = w.val → v = w := by
  intro h
  cases v
  cases w
  simp only at h
  simp only [h]

@[simp]
def nil : Vec α 0 := ⟨ [], rfl ⟩

@[simp]
def map (f: α → β) (v : Vec α n) : Vec β n :=
  ⟨ v.val.map f, by rw [List.length_map, v.prop] ⟩

end Vec
