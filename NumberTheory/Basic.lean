import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-- A binary operation on a type `X` maps two elements of `X` to another element of `X`. -/
def isBinaryOp {X: Type} (op : X → X → X) : Prop :=
  ∀ (x₁ x₂ : X), op x₁ x₂ ∈ Set.univ

/-- A binary operation is associative if `(a * b) * c = a * (b * c)` for all elements a, b, c. -/
def isAssociative {X : Type} (op : X → X → X) : Prop :=
  ∀ (a b c : X), op (op a b) c = op a (op b c)

/-- A binary operation is commutative if `a * b = b * a` for all elements a, b. -/
def isCommutative {X : Type} (op : X → X → X) : Prop :=
  ∀ (a b : X), op a b = op b a

/-- An element `e` is an identity for operation `op` if `e * a = a * e = a` for all elements a. -/
def isIdentity {X : Type} (op : X → X → X) (e : X) : Prop :=
  ∀ (a : X), op e a = a ∧ op a e = a

/-- An element `a` has an inverse with respect to operation `op` and identity `e`
    if there exists an element `b` such that `a * b = b * a = e`. -/
def hasInverse {X : Type} (op : X → X → X) (e : X) (a : X) : Prop :=
  ∃ (b : X), op a b = e ∧ op b a = e

/--
A semigroup is a set with an associative binary operation.
-/
structure MySemiGroup (S : Type) where
  /-- The binary operation of the semigroup -/
  op : S → S → S
  /-- The operation is associative -/
  assoc : isAssociative op

/--
An Abelian semigroup (or commutative semigroup) is a semigroup whose operation is commutative.
-/
structure MyAbelianSemiGroup (S : Type) extends MySemiGroup S where
  /-- The operation is commutative -/
  comm : isCommutative op

/--
A monoid is a semigroup with an identity element.
-/
structure MyMonoid (M : Type) extends MySemiGroup M where
  /-- The identity element of the monoid -/
  id : M
  /-- The identity element satisfies the identity properties -/
  id_prop : isIdentity op id

/--
A group is a monoid where every element has an inverse.
-/
structure MyGroup (G : Type) extends MyMonoid G where
  /-- The inverse operation that maps each element to its inverse -/
  inv : G → G
  /-- Every element multiplied by its inverse equals the identity -/
  inv_prop : ∀ a : G, op a (inv a) = id ∧ op (inv a) a = id

/--
An Abelian group (or commutative group) is a group whose operation is commutative.
-/
structure MyAbelianGroup (G : Type) extends MyGroup G where
  /-- The operation is commutative -/
  comm : isCommutative op

/--
Returns the order (number of elements) of a finite type.
-/
def myOrderOf {H : Type} [Fintype H] : ℕ := Fintype.card H

/--
A ring is an algebraic structure with two operations, addition and multiplication,
where addition forms an Abelian group and multiplication forms a monoid,
with multiplication distributing over addition.
-/
structure MyRing (R : Type) where
  /-- Addition operation -/
  add : R → R → R
  /-- Multiplication operation -/
  mul : R → R → R
  /-- Additive identity (zero) -/
  zero : R
  /-- Multiplicative identity (one) -/
  one : R
  /-- Addition is associative -/
  add_assoc : isAssociative add
  /-- Addition is commutative -/
  add_comm : isCommutative add
  /-- Zero is the additive identity -/
  add_id : isIdentity add zero
  /-- Every element has an additive inverse -/
  add_inv : R → R
  /-- The additive inverse property -/
  add_inv_prop : ∀ a : R, add a (add_inv a) = zero ∧ add (add_inv a) a = zero
  /-- Multiplication is associative -/
  mul_assoc : isAssociative mul
  /-- One is the multiplicative identity -/
  mul_id : isIdentity mul one
  /-- Left distributivity of multiplication over addition -/
  left_distrib : ∀ x y z : R, mul x (add y z) = add (mul x y) (mul x z)
  /-- Right distributivity of multiplication over addition -/
  right_distrib : ∀ x y z : R, mul (add x y) z = add (mul x z) (mul y z)

/--
A field is a commutative ring where every non-zero element has a multiplicative inverse.
-/
structure MyField (F : Type) extends MyRing F where
  /-- Multiplication is commutative -/
  mul_comm : isCommutative mul
  /-- Zero and one are distinct elements -/
  zero_ne_one : zero ≠ one
  /-- Multiplicative inverse for non-zero elements -/
  mul_inv : {a : F // a ≠ zero} → F
  /-- The multiplicative inverse property -/
  mul_inv_prop : ∀ (a : F) (h : a ≠ zero),
    mul a (mul_inv ⟨a, h⟩) = one ∧ mul (mul_inv ⟨a, h⟩) a = one

def residueClass (a m : ℤ) : Set ℤ :=
  {b : ℤ | b % m = a % m}


theorem eq_of_mod_eq {a b m : ℤ} :
  a % m = b % m → residueClass a m = residueClass b m := by
  intro h
  ext x
  unfold residueClass
  simp only [Set.mem_setOf_eq]
  rw[h]

def isInvertible (a m : ℤ ) : Prop :=
  ∃ x : ℤ, (a * x) % m = 1
