Martin Escardo, December 2017 (but done much earlier on paper)

As discussed in the module Omniscience, Bishop's "limited principle of
omniscience" amount to the omniscience of the type ℕ, that is,

  Π \(p : ℕ → 𝟚) → (Σ \(n : ℕ) → p n ≡ ₀) + (Π \(n : ℕ) → p n ≡ ₁).

This is in general not a univalent proposition, because there may be
many n:ℕ with p n ≡ ₀. In univalent mathematics, we may get a
proposition by truncating the Σ to get the existential quantifier ∃
(see the Homotopy Type Theory book). Here instead we construct the
truncation directly, and call it LPO.

Using this and the module Prop-Tychonoff, we show that the function
type LPO→ℕ is searchable and hence omniscient, despite the fact that
LPO is undecided in our type theory.

(We needed to add new helper lemmas in the module
GenericConvergentSequence)

\begin{code}

open import UF-FunExt

module LPO (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import Two
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import GenericConvergentSequence
open import OmniscientTypes
open import NaturalsOrder

LPO : U₀ ̇
LPO = (x : ℕ∞) → decidable(Σ \(n : ℕ) → x ≡ under n)

LPO-is-prop : is-prop LPO
LPO-is-prop = Π-is-prop (fe U₀ U₀) f
 where
  a : (x : ℕ∞) → is-prop(Σ \n → x ≡ under n)
  a x (n , p) (m , q) = to-Σ-≡ (under-lc (p ⁻¹ ∙ q) , ℕ∞-is-set (fe U₀ U₀)_ _)

  f : (x : ℕ∞) → is-prop (decidable (Σ \n → x ≡ under n))
  f x = decidable-is-prop (fe U₀ U₀) (a x)

\end{code}

We now show that LPO is logically equivalent to its traditional
formulation, which is the omniscience of ℕ. However, the traditional
formulation is not a univalent proposition in general, and hence not
type equivalent.

\begin{code}

LPO-gives-omniscient-ℕ : LPO → omniscient ℕ
LPO-gives-omniscient-ℕ lpo β = cases a b d
  where
    A = (Σ \(n : ℕ) → β n ≡ ₀) + (Π \(n : ℕ) → β n ≡ ₁)

    α : ℕ → 𝟚
    α = force-decreasing β

    x : ℕ∞
    x = (α , force-decreasing-is-decreasing β)

    d : decidable(Σ \(n : ℕ) → x ≡ under n)
    d = lpo x

    a : (Σ \(n : ℕ) → x ≡ under n) → A
    a (n , p) = inl (force-decreasing-is-not-much-smaller β n c)
      where
        c : α n ≡ ₀
        c = ap (λ - → incl - n) p ∙ under-diagonal₀ n

    b : (¬ Σ \(n : ℕ) → x ≡ under n) → A
    b u = inr g
      where
        v : (n : ℕ) → x ≡ under n → 𝟘
        v = curry u

        g : (n : ℕ) → β n ≡ ₁
        g n = force-decreasing-is-smaller β n e
          where
            c : x ≡ under n → 𝟘
            c = v n

            l : x ≡ ∞
            l = not-finite-is-∞ (fe U₀ U₀) v

            e : α n ≡ ₁
            e = ap (λ - → incl - n) l

omniscient-ℕ-gives-LPO : omniscient ℕ → LPO
omniscient-ℕ-gives-LPO chlpo x = cases a b d
  where
    A = decidable (Σ \(n : ℕ) → x ≡ under n)

    β : ℕ → 𝟚
    β = incl x

    d : (Σ \(n : ℕ) → β n ≡ ₀) + (Π \(n : ℕ) → β n ≡ ₁)
    d = chlpo β

    a : (Σ \(n : ℕ) → β n ≡ ₀) → A
    a (n , p) = inl (pr₁ g , pr₂(pr₂ g))
      where
        g : Σ \(m : ℕ) → (m ≤ n) × (x ≡ under m)
        g = under-lemma (fe U₀ U₀) x n p

    b : (Π \(n : ℕ) → β n ≡ ₁) → A
    b φ = inr g
      where
        ψ : ¬ Σ \(n : ℕ) → β n ≡ ₀
        ψ = uncurry (λ n → Lemma[b≡₁→b≢₀](φ n))

        f : (Σ \(n : ℕ) → x ≡ under n) → Σ \(n : ℕ) → β n ≡ ₀
        f (n , p) = (n , (ap (λ - → incl - n) p ∙ under-diagonal₀ n))
          where
           l : incl x n ≡ incl (under n) n
           l = ap (λ - → incl - n) p

        g : ¬ Σ \(n : ℕ) → x ≡ under n
        g = contrapositive f ψ

\end{code}

Now, if LPO is false, that is, an empty type, then the function type

  LPO → ℕ

is isomorphic to the unit type 𝟙, and hence is searchable and
omniscient. If LPO holds, that is, LPO is isomorphic to 𝟙 because it
is a univalent proposition, then the function type LPO → ℕ is
isomorphic to ℕ, and hence the type LPO → ℕ is again searchable by
LPO. So in any case we have that the type LPO → ℕ is
searchable. However, LPO is an undecided proposition in our type
theory, so that the nature of the function type LPO → ℕ is
undecided. Nevertheless, we can show that it is searchable, without
knowing whether LPO holds or not!

\begin{code}

open import SearchableTypes
open import PropTychonoff

LPO-gives-ℕ-searchable : searchable(LPO → ℕ)
LPO-gives-ℕ-searchable = prop-tychonoff-corollary' fe LPO-is-prop f
 where
   f : LPO → searchable ℕ
   f = inhabited-omniscient-implies-searchable 0 ∘ LPO-gives-omniscient-ℕ

LPO-gives-ℕ-omniscient : omniscient(LPO → ℕ)
LPO-gives-ℕ-omniscient = searchable-implies-omniscient LPO-gives-ℕ-searchable

\end{code}

Another condition equivalent to LPO is that under𝟙 has a section:

\begin{code}

has-section-under𝟙-gives-LPO : (Σ \(s : ℕ∞ → ℕ + 𝟙) → under𝟙 ∘ s ∼ id) → LPO
has-section-under𝟙-gives-LPO (s , ε) u = ψ (s u) refl
 where
  ψ : (z : ℕ + 𝟙) → s u ≡ z → decidable(Σ \(n : ℕ) → u ≡ under n)
  ψ (inl n) p = inl (n , (u            ≡⟨ (ε u) ⁻¹ ⟩
                          under𝟙 (s u) ≡⟨ ap under𝟙 p ⟩
                          under n      ∎))
  ψ (inr *) p = inr γ
   where
    γ : ¬ Σ \(n : ℕ) → u ≡ under n
    γ (n , q) = ∞-is-not-finite n (∞            ≡⟨ (ap under𝟙 p)⁻¹ ⟩
                                   under𝟙 (s u) ≡⟨ ε u ⟩
                                   u            ≡⟨ q ⟩
                                   under n      ∎)

under𝟙-inverse : (u : ℕ∞) → decidable(Σ \(n : ℕ) → u ≡ under n) → ℕ + 𝟙 {U₀}
under𝟙-inverse .(under n) (inl (n , refl)) = inl n
under𝟙-inverse u (inr g) = inr *

under𝟙-inverse-inl : (u : ℕ∞) (d : decidable(Σ \(n : ℕ) → u ≡ under n))
                   → (m : ℕ) → u ≡ under m → under𝟙-inverse u d ≡ inl m
under𝟙-inverse-inl .(under n) (inl (n , refl)) m q = ap inl (under-lc q)
under𝟙-inverse-inl u (inr g) m q = 𝟘-elim (g (m , q))


LPO-gives-has-section-under𝟙 : LPO → Σ \(s : ℕ∞ → ℕ + 𝟙) → under𝟙 ∘ s ∼ id
LPO-gives-has-section-under𝟙 lpo = s , ε
 where
  s : ℕ∞ → ℕ + 𝟙
  s u = under𝟙-inverse u (lpo u)
  φ : (u : ℕ∞) (d : decidable (Σ \(n : ℕ) → u ≡ under n)) → under𝟙 (under𝟙-inverse u d) ≡ u
  φ .(under n) (inl (n , refl)) = refl
  φ u (inr g) = (not-finite-is-∞ (fe U₀ U₀) (curry g))⁻¹
  ε : under𝟙 ∘ s ∼ id
  ε u = φ u (lpo u)

\end{code}
