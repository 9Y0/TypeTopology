Arithmetic via equivalence
--------------------------

Martín Hötzel Escardó

Originally 10 July 2014, modified 10 Oct 2017, 22 March 2018.

This is a literate proof in univalent mathematics, in Agda notation.

We have that 3+3+3+3+3 = 5+5+5, or 5×3 = 3×5, and more generally

  m×n = n×m.

This can of course be proved by induction. A more appealing pictorial
proof is

  ooo
  ooo         ooooo
  ooo    =    ooooo
  ooo         ooooo
  ooo

where "o" is an pebble. We just rotate the grid of pebbles, or swap
the coordinates, and doing this doesn't change the number of pebbles.

How can this proof be formally rendered, as faithfully as possible to
the intuition?

We first define an interpretation function Fin : ℕ → Set of numbers as
sets by

 (1) Fin   0  = 𝟘,          where 𝟘 is the empty set,
 (2) Fin(n+1) = Fin n + 𝟙,  where 𝟙 is the singleton set, 

Then Fin is a semiring homomorphism:

 (3) Fin(m + n) ≃ Fin m + Fin n, where "+" in the rhs is disjoint union, 
 (4) Fin 1 ≃ 𝟙,
 (5) Fin(m × n) ≃ Fin m × Fin n, where "×" in the rhs is cartesian product,

It is also left-cancellable:

 (6) Fin m ≃ Fin n → m = n.

But instead of proving (3)-(5) after defining addition and
multiplication, we prove that

 (3') For every m,n:ℕ there is k:ℕ with Fin k ≃ Fin m + Fin n.
 (5') For every m,n:ℕ there is k:ℕ with Fin k ≃ Fin m × Fin n. 

We then define addition and multiplication on ℕ from (3') and (5'),
from which (3) and (5) follow tautologically.

This relies on type arithmetic. To prove (3'), we use the trivial
equivalences
 
 X ≃ X + 𝟘,
 (X + Y) + 𝟙 ≃ X + (Y + 𝟙),

mimicking the definition of addition on ℕ in Peano arithmetic (but
with the equations written backwards).

To prove (4), we use the equivalence

 𝟘 + 𝟙 ≃ 𝟙

To prove (5'), we use the equivalences

 𝟘 ≃ X × 𝟘,
 X × Y + X ≃ X × (Y + 𝟙),

mimicking the definition of multiplication on ℕ in Peano arithmetic
(again backwards).

To prove the cancellation property (6), we use the cancellation
property

 X + 𝟙 ≃ Y + 𝟙 → X ≃ Y,

mimicking the cancellation property of the successor function on ℕ.
(This is the only combinatorial argument here.)

Now, relying on the equivalence

 X × Y ≃ Y × X,

which corresponds to the rotation of the grid of pebbles, we can prove
m × n = n × m as follows:

 Fin(m × n) ≃ Fin m × Fin n   by (5)
            ≃ Fin n × Fin m   by  X × Y ≃ Y × X,
            ≃ Fin(n × m)      by (5),

and so 

 m × n ≃ n × m                by (6).

Similarly we can prove, of course,

 m + n ≃ n + m

using (3) and the equivalence

 X + Y ≃ Y + X.

Among all these constructions, we use induction on ℕ only in

  * the definition (1-2) of the function Fin : ℕ → Set,

  * the existence (3')-(5') of addition and multiplication, and

  * the left-cancellability (6) of Fin.

With this, induction is not needed to prove that addition and
multiplication are commutative.

Side-remark, to be explored in a future version. From the equivalence

 (5) Fin(m × n) ≃ Fin m × Fin n

we get two maps

     f : Fin(m × n) → Fin m,
     g : Fin(m × n) → Fin n,

which we didn't define explicitly or combinatorially.

21st March 2018 remark: After doing this, I found this article by Tim
Gowers:

    Why is multiplication commutative?
    https://www.dpmms.cam.ac.uk/~wtg10/commutative.html

which says very much the same as above (implemented below in univalent
foundations in Agda notation).

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import UF

module ArithmeticViaEquivalence (fe : ∀ U V → FunExt U V) where

open import EquivalenceExamples
open import Naturals
open import PlusOneLC

\end{code}

1st definition by induction. From a natural number n, get a finite set
with n elements. This can be considered as an interpretation function,
which defines the meaning of numbers as types.

\begin{code}

Fin : ℕ → U₀ ̇
Fin zero     = 𝟘
Fin (succ n) = Fin n + 𝟙

\end{code}

We have zero and successor for finite sets, with the following types:

\begin{code}

fzero : {n : ℕ} → Fin(succ n)
fzero = inr *

fsucc : {n : ℕ} → Fin n → Fin(succ n)
fsucc = inl

\end{code}

2nd definition by induction. Existence of addition:

\begin{code}

+construction : (m n : ℕ) → Σ \(k : ℕ) → Fin k ≃ (Fin m + Fin n)
+construction m zero = m , 𝟘-rneutral
+construction m (succ n) = goal
  where
    IH : Σ \(k : ℕ) → Fin k ≃ (Fin m + Fin n)
    IH = +construction m n
    k : ℕ
    k = pr₁ IH
    φ : Fin k ≃ (Fin m + Fin n)
    φ = pr₂ IH
    φ+𝟙 : Fin(succ k) ≃ (Fin m + Fin (succ n))
    φ+𝟙 = ≃-trans (Ap+ 𝟙 φ) +assoc
    goal : Σ \(k' : ℕ) → Fin k' ≃ (Fin m + Fin (succ n))
    goal = succ k , φ+𝟙

\end{code}

The construction gives an addition function by projection:

\begin{code}

_+'_ : ℕ → ℕ → ℕ
m +' n = pr₁(+construction m n)

\end{code}

The construction also shows that its satisfies the usual
characterizing equations from Peano arithmetic:

\begin{code}

+base : {m : ℕ} → m +' zero ≡ m
+base = refl

+step : {m n : ℕ} → m +' (succ n) ≡ succ(m +' n)
+step = refl

\end{code}

Tautologically, we get that Fin : ℕ → Type is an
addition-homomorphism:

\begin{code}

Fin+homo' : (m n : ℕ) → Fin(m +' n) ≃ (Fin m + Fin n)
Fin+homo' m n = pr₂(+construction m n)

\end{code}

3rd and last definition by induction. The function Fin : ℕ → Type is
left-cancellable:

\begin{code}

flc-construction : (m n : ℕ) → Fin m ≃ Fin n → m ≡ n
flc-construction zero zero p = refl
flc-construction (succ m) zero p = 𝟘-elim absurd
 where
  remark : (Fin m + 𝟙) ≃ 𝟘
  remark = p
  absurd : 𝟘
  absurd = eqtofun _ _ p fzero
flc-construction zero (succ n) p = 𝟘-elim absurd
 where
  remark : 𝟘 ≃ (Fin n + 𝟙)
  remark = p
  absurd : 𝟘 
  absurd = eqtofun _ _ (≃-sym p) fzero
flc-construction (succ m) (succ n) p = ap succ r
 where
  IH : Fin m ≃ Fin n → m ≡ n
  IH = flc-construction m n
  remark : (Fin m + 𝟙) ≃ (Fin n + 𝟙)
  remark = p
  q : Fin m ≃ Fin n
  q = +𝟙-cancellable fe p
  r : m ≡ n
  r = IH q 

\end{code}

This uses the non-trivial construction +𝟙-cancellable defined in the
module PlusOneLC.lagda.

With this, no further induction is needed to prove commutativity of
addition:

\begin{code}

+'-comm : (m n : ℕ) → m +' n ≡ n +' m
+'-comm m n = flc-construction (m +' n) (n +' m) p
 where
  p : Fin(m +' n) ≃ Fin(n +' m)
  p = ≃-trans (Fin+homo' m n) (≃-trans +comm (≃-sym (Fin+homo' n m)))

\end{code}

We now repeat this story for multiplication:

\begin{code}

×construction : (m n : ℕ) → Σ \(k : ℕ) → Fin k ≃ Fin m × Fin n
×construction m zero = zero , ×𝟘
×construction m (succ n) = goal
  where
    IH : Σ \(k : ℕ) → Fin k ≃ Fin m × Fin n
    IH = ×construction m n
    k : ℕ
    k = pr₁ IH
    φ : Fin k ≃ Fin m × Fin n
    φ = pr₂ IH
    φ' : Fin (k +' m) ≃ Fin m × (Fin n + 𝟙)
    φ' = ≃-trans (Fin+homo' k m) (≃-trans (Ap+ (Fin m) φ) 𝟙distr)
    goal : Σ \(k' : ℕ) → Fin k' ≃ Fin m × Fin (succ n)
    goal = (k +' m) , φ'

_×'_ : ℕ → ℕ → ℕ
m ×' n = pr₁(×construction m n)

×base : {m : ℕ} → m ×' zero ≡ zero
×base = refl

×step : {m n : ℕ} → m ×' (succ n) ≡ m ×' n +' m
×step = refl

Fin×homo : (m n : ℕ) → Fin(m ×' n) ≃ Fin m × Fin n
Fin×homo m n = pr₂(×construction m n)

×-comm : (m n : ℕ) → m ×' n ≡ n ×' m
×-comm m n = flc-construction (m ×' n) (n ×' m) φ
 where
  φ : Fin(m ×' n) ≃ Fin(n ×' m)
  φ = ≃-trans (Fin×homo m n) (≃-trans ×comm (≃-sym (Fin×homo n m)))

\end{code}

\begin{code}

infixl 20 _+'_ 
infixl 22 _×'_ 

\end{code}
