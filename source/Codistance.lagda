Martin Escardo, 11th September 2018

We begin by defining a "codistance" or "closeness" function

  c : X → X → ℕ∞

such that

  c x y ≡ ∞ ⇔ x ≡ y

for some examples of types X, including Baire, Cantor and ℕ∞.

That is, two points are equal iff they are infinitely close.  If we
have c x y ≡ under n for n : ℕ, the intuition is that x and y can be
distinguished by a finite amount of information of size n.

We then discuss further codistance axioms.

(An application is to show that WLPO holds iff ℕ∞ is discrete.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module Codistance (fe : ∀ U V → funext U V) where

open import Two
open import Sequence fe
open import CoNaturals fe
open import GenericConvergentSequence
open import DiscreteAndSeparated
open import UF-SetExamples

module sequences
        {U : Universe}
        (D : U ̇)
        (δ : discrete D)
       where

\end{code}

We denote the type of sequences over D by $:

\begin{code}

 private
   $ : U ̇
   $ = ℕ → D
   X : U ̇
   X = $ × $
   f : (α β : $) → head α ≡ head β → 𝟙 {U₀} + X
   f α β q = inr (tail α , tail β)
   g : (α β : $) → head α ≢ head β → 𝟙 {U₀} + X
   g α β n = inl *
   p : X → 𝟙 {U₀} + X
   p (α , β) = cases (f α β) (g α β) (δ (head α) (head β))
   c : $ → $ → ℕ∞
   c α β = ℕ∞-corec p (α , β)

 codistance : $ → $ → ℕ∞
 codistance = c

 codistance-Zero : (α β : $) → head α ≢ head β → c α β ≡ Zero
 codistance-Zero α β n = γ r
  where
   t : δ (head α) (head β) ≡ inr n
   t = discrete-inr (fe U U₀) δ (head α) (head β) n
   r : p (α , β) ≡ inl *
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inl * → c α β ≡ Zero
   γ = coalg-morphism-Zero p (λ {(α , β) → c α β}) (ℕ∞-corec-diagram p) (α , β) *

 codistance-Succ : (α β : $) → head α ≡ head β → c α β ≡ Succ(c (tail α) (tail β))
 codistance-Succ α β q = γ r
  where
   t : δ (head α) (head β) ≡ inl q
   t = discrete-inl δ (head α) (head β) q
   r : p (α , β) ≡ inr (tail α , tail β)
   r = ap (cases (f α β) (g α β)) t
   γ : p (α , β) ≡ inr (tail α , tail β) → c α β ≡ Succ (c (tail α) (tail β))
   γ = coalg-morphism-Succ p (λ {(α , β) → c α β}) (ℕ∞-corec-diagram p) (α , β) (tail α , tail β)

 si : (α : $) → c α α ≡ ∞
 si α = ℕ∞-coinduction R b (c α α) ∞ γ
  where
   l : ∀ α → c α α ≡ Succ (c (tail α) (tail α))
   l α = codistance-Succ α α refl
   R : ℕ∞ → ℕ∞ → U ̇
   R u v = (Σ \(α : $) → u ≡ c α α) × (v ≡ ∞)
   b : ℕ∞-bisimulation R
   b .(c α α) .∞ ((α , refl) , refl) = s , t , Pred-∞-is-∞
    where
     s : positivity (c α α) ≡ positivity ∞
     s = successors-same-positivity (l α) ((Succ-∞-is-∞ (fe U₀ U₀))⁻¹)
     t : Σ (\(α' : $) → Pred (c α α) ≡ c α' α')
     t = tail α , (ap Pred (l α) ∙ Pred-Succ)
   γ : R (c α α) ∞
   γ = (α , refl) , refl

 iae : (α β : $) → c α β ≡ ∞ → α ≡ β
 iae = seq-coinduction (λ α β → c α β ≡ ∞) b
  where
   b : (α β : $) → c α β ≡ ∞
                 → (head α ≡ head β) × (c (tail α) (tail β) ≡ ∞)
   b α β q = d , e
    where
     l : head α ≢ head β → c α β ≡ Zero
     l = codistance-Zero α β
     d : head α ≡ head β
     d = Cases (δ (head α) (head β))
          (λ (p : head α ≡ head β)
                → p)
          (λ (n : head α ≢ head β)
                → 𝟘-elim (Zero-not-Succ (Zero    ≡⟨ (l n)⁻¹ ⟩
                                         c α β   ≡⟨ q ⟩
                                         ∞       ≡⟨ (Succ-∞-is-∞ (fe U₀ U₀))⁻¹ ⟩
                                         Succ ∞  ∎)))
     e : c (tail α) (tail β) ≡ ∞
     e = ap Pred (Succ (c (tail α) (tail β)) ≡⟨ (codistance-Succ α β d)⁻¹ ⟩
                  c α β                      ≡⟨ q ⟩
                  ∞                          ∎)

\end{code}

We now consider the following two special cases:

\begin{code}

open sequences ℕ ℕ-discrete
      renaming
        (codistance to Baire-codistance ;
         si         to Baire-si ;
         iae        to Baire-iae)

open sequences 𝟚 𝟚-discrete
      renaming
        (codistance to Cantor-codistance ;
         si         to Cantor-si ;
         iae        to Cantor-iae)

\end{code}

And now we reduce the codistance of the Cantor type to the generic
convergent sequence:

\begin{code}

ℕ∞-codistance : ℕ∞ → ℕ∞ → ℕ∞
ℕ∞-codistance u v = Cantor-codistance (incl u) (incl v)

ℕ∞-si : (u : ℕ∞) → ℕ∞-codistance u u ≡ ∞
ℕ∞-si u = Cantor-si (incl u)

ℕ∞-iae : (u v : ℕ∞) → ℕ∞-codistance u v ≡ ∞ → u ≡ v
ℕ∞-iae u v r = incl-lc (fe U₀ U₀) γ
 where
  γ : incl u ≡ incl v
  γ = Cantor-iae (incl u) (incl v) r

\end{code}

TODO. Complete the proof of the codistance axioms for the above
codistances on Baire, Cantor and ℕ∞, according to the following
initial template:

\begin{code}

{-
minℕ∞ : ℕ∞ → ℕ∞ → ℕ∞
minℕ∞ = {!!}
-}

is-codistance
 indistinguishable-are-equal
 self-indistinguishable
 is-symmetric
 -- is-ultra
  : ∀ {U} {X : U ̇} → (X → X → ℕ∞) → U ̇

indistinguishable-are-equal c = ∀ x y → c x y ≡ ∞ → x ≡ y
self-indistinguishable      c = ∀ x → c x x ≡ ∞
is-symmetric                c = ∀ x y → c x y ≡ c y x
-- is-ultra                 c = ∀ x y z → minℕ∞ (c x y) (c y z) ≼ c x z
is-codistance               c = indistinguishable-are-equal c
                              × self-indistinguishable c
                              × is-symmetric c
--                            × is-ultra c

\end{code}
