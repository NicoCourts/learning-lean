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

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry