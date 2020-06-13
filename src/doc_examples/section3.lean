constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp 

theorem t1' : p→ q → p :=
begin
    intros hp hq,
    exact hp,
end

theorem t1'' (hp : p) (hq : q) : p := hp

axiom hp : p
theorem t2 : q → p := t1' hp

-- Quantify over all propositions
theorem t1''' (p q : Prop) (hp : p) (hq : q): p := hp

#check t1'''
#check t1''

variables r s : Prop
#check t1''' r
#check t1''' r s

#check assume (hp : p) (hq : q), and.intro hp hq
example (hp : p) (hq :q) : p ∧ q := ⟨hp, hq⟩

-- SYNTACTIC SUGAR
variable l : list ℕ
#check l.head
#check list.head l
--chef's kiss

-- OR
example (h : p ∨ q) : q ∨ p := 
or.elim 
h                 -- proof of p ∨ q
(λ hp, or.inr hp) -- proof of p → q ∨ p
(λ hq, or.inl hq) -- proof of q → q ∨ p

-- True and False
-- Neat lingo!
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
absurd -- You are
(hqp hq) -- (proof of q → p)(proof of q) = proof of p
hnp -- proof of ¬p

example (hp : p) : true := trivial -- Nice

-- IFF
theorem and_swap : p ∧ q ↔ q ∧ p :=
iff.intro 
(λ h : p ∧ q, and.intro h.right h.left) 
(λ h : q ∧ p, and.intro h.right h.left)


---------------------
---------------------
---------------------

-- Ex 1
variables p q  : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := iff.intro 
(λ h : p ∧ q, and.intro h.right h.left) 
(λ h : q ∧ p, and.intro h.right h.left)

example : p ∨ q ↔ q ∨ p := iff.intro 
(λ h: p ∨ q, or.elim h or.inr or.inl) 
(λ h: q ∨ p, or.elim h or.inr or.inl) 

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := iff.intro
(λ x : (p ∧ q) ∧ r, and.intro x.1.1 (and.intro x.1.2 x.2))
(λ x : p ∧ (q ∧ r), and.intro (and.intro x.1 x.2.1) x.2.2)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := iff.intro
(λ x : (p ∨ q) ∨ r, or.elim x 
  (λ y : p ∨ q, or.elim y or.inl (λ z : q, or.inr (or.inl z)))
  (λ y : r, or.intro_right p (or.intro_right q y))
)
(λ x : p ∨ (q ∨ r), or.elim x 
  (λ y : p, or.intro_left r (or.intro_left q y))
  (λ y : q ∨ r, or.elim y (λ z : q, or.inl (or.inr z)) or.inr)
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := iff.intro
(λ x, and.elim x
  (λ a b, or.elim b 
    (λ z, or.inl (and.intro a z)) 
    (λ z, or.inr (and.intro a z))
  )
)
(λ x, or.elim x 
  (λ y, have q ∨ r, from or.inl y.right, and.intro y.left this)
  (λ y, have q ∨ r, from or.inr y.right, and.intro y.left this)
)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := iff.intro
(λ x, or.elim x
  (λ z, and.intro (or.inl z) (or.inl z))
  (λ z, z.elim 
    (λ a b, and.intro (or.inr z.1) (or.inr z.2)) 
  )
)
(λ x, and.elim x
  (λ y z, or.elim y 
    (λ a, or.inl a)
    (λ b, or.elim z 
      (λ a, or.inl a)
      (λ c, or.inr (and.intro b c))
    )
  )
)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := iff.intro 
(λ a b, a (b.1) (b.2))
(λ a b c, a (and.intro b c))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := iff.intro 
(λ x, and.intro 
  (λ y, x (or.inl y))
  (λ y, x (or.inr y))
)
(λ x y, or.elim y
  (λ z, x.1 z)
  (λ z, x.2 z)
)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := iff.intro 
(λ x, and.intro 
  (λ y, x (or.inl y))
  (λ y, x (or.inr y))
)
(λ x y, or.elim y
  (have z:p, from or.elim y (λ x,x) (λ z, absurd z x.2 ), absurd z x.1)
  (λ z, absurd z x.2)
)

example : ¬p ∨ ¬q → ¬(p ∧ q) := λ x y, or.elim x (absurd y.1) (absurd y.2)

example : ¬(p ∧ ¬p) := λ x, absurd x.1 x.2

example : p ∧ ¬q → ¬(p → q) := λ x y, absurd (y x.1) x.2

example : ¬p → (p → q) := λ x y, absurd y x

example : (¬p ∨ q) → (p → q) := λ x y, or.elim x (λ z, absurd y z) (λ x, x)

example : p ∨ false ↔ p := iff.intro 
(λ x, x.elim (λ y, y) (λ y, have ¬ false, from (λ z, z), (absurd y this))) 
(λ x, or.inl x)

example : p ∧ false ↔ false := iff.intro
(λ x, x.2)
(λ x, have s :p, from (have s: ¬false, from (λ z, z), (absurd x s)), and.intro s x)

example : (p → q) → (¬q → ¬p) := λ x y z, absurd (x z) y

-- Ex 3
-- Not supposed to have classical open, so I am doing it first. :)
example : ¬(p ↔ ¬p) := (λ x, 
  have h : p → ¬p, from (iff.elim_left x), 
  have h' : ¬p → p, from (iff.elim_right x),
  have k : p → false, from (assume h'' : p, absurd h'' (h h'')),
  have k': p, from (h' k),
  absurd k' k
) 

-- Ex 2
open classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := λ x, by_cases
  (assume h : r, have h1: p → r, from (λ x, h), or.inl h1)
  (assume h : ¬r, have h1: p → s, from 
    (λ z, or.elim (x z) 
      (λ w, (absurd w h)) 
      (have h2 : p → s, from or.elim (x z) (λ t, absurd t h) (λ a b, a), λ a, a)
    ),
    or.inr h1
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q := λ x, by_cases 
  (assume h : p, (by_cases 
    (assume h': q, absurd (and.intro h h') x)
    (assume h': ¬q, or.inr h')
  ))
  (assume h : ¬p, or.inl h)

example : ¬(p → q) → p ∧ ¬q := λ x, by_cases 
(assume h : q, have h1 : p → q, from (λ _, h), absurd h1 x) 
(assume h: ¬q, by_cases 
  (assume s : p, and.intro s h)
  (assume s : ¬p, have h1: p → q, from (λ a, absurd a s), absurd h1 x)
)

example : (p → q) → (¬p ∨ q) := λ x, by_cases 
(assume h : p, or.inr (x h))
(assume h : ¬p, or.inl h)

example : (¬q → ¬p) → (p → q) := λ x y, by_cases
(assume h : q, h)
(assume h : ¬q, absurd y (x h))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := by_cases 
(assume h : p, λ _, h)
(assume h : ¬p, λ x, have h1 : p → q, from (λ y, absurd y h), x h1)


