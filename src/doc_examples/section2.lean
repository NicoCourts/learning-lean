def mul : ℕ→ℕ→ℕ := λ x y, x*y

--- Dependent Types
namespace hidden

universe u

constant list   : Type u → Type u

constant cons   : Π α : Type u, α → list α → list α
constant nil    : Π α : Type u, list α
constant head   : Π α : Type u, list α → α
constant tail   : Π α : Type u, list α → list α
constant append : Π α : Type u, list α → list α → list α

end hidden


--------------------
--------------------
--------------------
-- Ex 1

def Do_Twice : ((ℕ→ℕ)→ (ℕ→ℕ)) → (ℕ→ℕ) → ℕ → ℕ := λ F f, F (F f)
def do_twice : (ℕ→ℕ) → ℕ → ℕ := λ f x, f (f x)

#reduce Do_Twice do_twice (mul 2)

-- Ex 2

def curry (α β γ : Type) (f : α × β → γ) : α → β → γ := λ a b, f(a,b)

def uncurry (α β γ : Type) (f : α → β → γ) : α × β → γ := λ x, f x.1 x.2

def curry_mul := uncurry ℕ ℕ ℕ mul
#reduce curry_mul (2,3)
def mul' := curry ℕ ℕ ℕ curry_mul

lemma lem : ∀ a b : ℕ, mul a b = mul' a b :=
begin
    intros a b,
    refl,
end

-- Ex 3

universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
  constant vec_add : Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n
  constant vec_reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n
end vec

constant α : Type
constant a : α
constants m n r : ℕ
constants v w : vec α n

#check vec.vec_add v w 
#check vec.vec_reverse v 

-- Ex 4
constant matrix : Type u → ℕ → ℕ → Type u 

namespace matrix
  constant mat_mult : Π {α : Type u} {m n r : ℕ}, matrix α m n → matrix α n r → matrix α m r
  constant mat_add : Π {α : Type u} {m n :ℕ}, matrix α m n → matrix α m n → matrix α m n
end matrix

/-
    The question says to define matrices and then multiplication of vec and a 
    matrix. But a vec is just a (let's say column) matrix...
-/

def vec' := λ β x, matrix β 1 x 
#check vec'
#check vec

