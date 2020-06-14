
import algebra.ordered_ring

import tactic

---------------------
---------------------
---------------------

-- Ex 1
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := iff.intro
(λ h, 
  have h' : (∀ x : α, p x), from (assume y : α, (h y).1),
  have h'' : (∀ x : α, q x), from (assume y : α, (h y).2),
  and.intro h' h'')
(λ h y, and.intro (h.1 y) (h.2 y))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
(λ x y, assume s : α, ((x s) (y s)))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
(λ h, assume s:α, h.elim 
  (λ h', or.inl (h' s))
  (λ h', or.inr (h' s))
)

-- Ex 2 
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := (λ t, iff.intro
  (λ f, f t)
  (λ s _, s)
)

section LEM
open classical -- Need LEM for half of this

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := iff.intro
  (by_cases 
    (assume s : r, λ _, or.inr s) 
    (assume s: ¬r, λ h, or.inl (assume z : α, (h z).elim 
      (λ w, w) 
      (λ h', absurd h' s)
    ))
  )
  (λ h, assume y : α, h.elim (λ t, or.inl (t y)) (or.inr))

end LEM

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := iff.intro 
  (λ h a, assume s : α, (h s a)) 
  (λ h, assume s:α, λ t, (h t s))

-- Ex 3
variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

-- Used the solver because I already solved this essentially
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=  have p: (shaves barber barber ↔ ¬shaves barber barber), from h barber,
  (not_iff_self (shaves barber barber)).mp (iff.symm (h barber))

-- Ex 4
namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
end

end hidden

def prime (n : ℕ) : Prop := ∀ a b : ℕ, (hidden.divides n (a*b) → (hidden.divides n a ∨ hidden.divides n b))

def infinitely_many_primes : Prop := (∀ p : ℕ, (prime p) → (∃ m : ℕ, (p < m) ∧ prime m))

def Fermat_prime (n : ℕ) : Prop := ∃ k : ℕ, (n = 2^(2^k)) ∧ prime n

def infinitely_many_Fermat_primes : Prop := (∀ p : ℕ, (Fermat_prime p) → (∃ m : ℕ, (p < m) ∧ Fermat_prime m))

def goldbach_conjecture : Prop := ∀ n : ℕ, (3 ≤ n) → (∃ p q :ℕ, (prime p) ∧ (prime q) ∧ (n = p + q))

def Goldbach's_weak_conjecture : Prop := ∀ k, (2≤ k) → (∃ p q r : ℕ, (prime p) ∧ (prime q) ∧ (prime r) ∧ (2*k+1=p+q+r))

def Fermat's_last_theorem : Prop := ∀ n : ℕ, 3 ≤ n → ¬∃ a b c :ℕ, a^n+b^n=c^n

-- Ex 5

section EX5
open classical

variable a : α

example : (∃ x : α, r) → r := assume ⟨ x, hr ⟩, hr 

example : r → (∃ x : α, r) := λ h, exists.intro a h 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := iff.intro
(λ h, exists.elim h (λ a b, and.intro ⟨a, b.1⟩  b.2))
(λ h, exists.elim h.1 (λ b h', ⟨b,and.intro h' h.2⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end EX5


-- Ex 6

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y := calc
  log (x * y) = log (exp (log x) * exp (log y))     : by rw [exp_log_eq hx, exp_log_eq hy]
          ... = log (exp (log x + log y))           : by rw [exp_add (log x) (log y)]
          ... = log x + log y                       : by rw [log_exp_eq]

-- Ex 7
#check sub_self

example (x : ℤ) : x * 0 = 0 := calc
  x * 0 = x * (1 - 1)   : by rw sub_self
   ...  = x * 1 - x * 1 : by rw mul_sub
   ...  = x - x         : by rw mul_one
   ...  = 0             : by rw sub_self
