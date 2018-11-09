Martin Escardo, 21 March 2018

We prove the known (constructive) fact that

  X + 𝟙 ≃ Y + 𝟙 → X ≃ Y.

The proof may be new (or not).

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import DiscreteAndSeparated

module PlusOneLC (fe : ∀ U V → funext U V) where

_∖_ : (X : U ̇) (a : X) → U ̇
X ∖ a = Σ \(x : X) → x ≢ a

add-and-remove-same-point : {X : U ̇} →  X ≃ (X + 𝟙) ∖ (inr *)
add-and-remove-same-point {U} {X} = qinveq f (g , ε , η)
 where
  f : X → (X + 𝟙 {U}) ∖ inr *
  f x = (inl x , λ ())
  g : (X + 𝟙) ∖ inr * → X
  g (inl x , u) = x
  g (inr * , u) = 𝟘-elim (u refl)
  η : f ∘ g ∼ id
  η (inl x , u) = to-Σ-≡' (negations-are-props (fe U U₀) _ _)
  η (inr * , u) = 𝟘-elim (u refl)
  ε : g ∘ f ∼ id
  ε x = refl

remove-points : {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → (a : X) → X ∖ a ≃ Y ∖ (f a)
remove-points {U} {V} {X} {Y} f (g , (ε , η)) a = qinveq f' (g' , ε' , η')
 where
  f' : X ∖ a → Y ∖ (f a)
  f' (x , u) = (f x , λ(p : f x ≡ f a) → u ((ε x)⁻¹ ∙ ap g p ∙ ε a))
  g' : Y ∖ (f a) → X ∖ a
  g' (y , v) = (g y , λ(p : g y ≡ a) → v ((η y) ⁻¹ ∙ ap f p))
  ε' : g' ∘ f' ∼ id
  ε' (x , _) = to-Σ-≡ (ε x , negations-are-props (fe U U₀) _ _)
  η' : f' ∘ g' ∼ id
  η' (y , _) = to-Σ-≡ (η y , negations-are-props (fe V U₀) _ _)

add-one-and-remove-isolated-point : ∀ {V} {Y : V ̇} (z : Y + 𝟙) → isolated z → ((Y + 𝟙) ∖ z) ≃ Y
add-one-and-remove-isolated-point {V} {Y} (inl b) i = qinveq f (g , ε , η)
 where
  f : (Y + 𝟙) ∖ (inl b) → Y
  f (inl y , u) = y
  f (inr * , u) = b
  g' : (y : Y) → decidable (inl b ≡ inl y) → (Y + 𝟙) ∖ (inl b)
  g' y (inl p) = (inr * , +disjoint')
  g' y (inr u) = (inl y , contrapositive (λ p → p ⁻¹) u)
  g : Y → (Y + 𝟙) ∖ (inl b)
  g y = g' y (i (inl y))
  ε : g ∘ f ∼ id
  ε (inl y , u) = to-Σ-≡ (p , negations-are-props (fe V U₀) _ _)
   where
    φ : (p : inl b ≡ inl y) (q : i (inl y) ≡ inl p) → i (inl y) ≡ inr (≢-sym u)
    φ p q = 𝟘-elim (u (p ⁻¹))
    ψ : (v : inl b ≢ inl y) (q : i (inl y) ≡ inr v) → i (inl y) ≡ inr (≢-sym u)
    ψ v q = q ∙ ap inr (negations-are-props (fe V U₀) _ _)
    h : i (inl y) ≡ inr (≢-sym u)
    h = equality-cases (i (inl y)) φ ψ
    p : pr₁(g' y (i (inl y))) ≡ inl y
    p = ap (pr₁ ∘ (g' y)) h
  ε (inr * , u) = equality-cases (i (inl b)) φ ψ
   where
    φ : (p : inl b ≡ inl b) → i (inl b) ≡ inl p → g (f (inr * , u)) ≡ (inr * , u)
    φ p q = r ∙ to-Σ-≡ (refl , negations-are-props (fe V U₀) _ _)
     where
      r : g b ≡ (inr * , +disjoint')
      r = ap (g' b) q
    ψ : (v : inl b ≢ inl b) → i (inl b) ≡ inr v → g (f (inr * , u)) ≡ (inr * , u)
    ψ v q = 𝟘-elim (v refl)
  η : f ∘ g ∼ id
  η y = equality-cases (i (inl y)) φ ψ
   where
    φ : (p : inl b ≡ inl y) → i (inl y) ≡ inl p → f (g' y (i (inl y))) ≡ y
    φ p q = ap (λ - → f (g' y -)) q ∙ inl-lc p
    ψ : (u : inl b ≢ inl y) → i (inl y) ≡ inr u → f (g' y (i (inl y))) ≡ y
    ψ _ = ap ((λ d → f (g' y d)))

add-one-and-remove-isolated-point {V} {Y} (inr *) _ = ≃-sym add-and-remove-same-point

+𝟙-cancellable : {X : U ̇} {Y : V ̇} → (X + 𝟙) ≃ (Y + 𝟙) → X ≃ Y
+𝟙-cancellable {U} {V} {X} {Y} (φ , e) =
   X                  ≃⟨ add-and-remove-same-point ⟩
  (X + 𝟙) ∖ inr *     ≃⟨ remove-points φ (equivs-are-qinvs φ e) (inr *) ⟩
  (Y + 𝟙) ∖ φ (inr *) ≃⟨ add-one-and-remove-isolated-point
                              (φ (inr *))
                              (equivalences-preserve-isolatedness φ e (inr *) isolated-added-point) ⟩
   Y ■

\end{code}

Precedences:

\begin{code}

infix 2 _∖_

\end{code}
