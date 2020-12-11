Martin Escardo, December 2020

A notion of disconnectedness. This is different from homotopy
disconnectedness in the sense of the HoTT book.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module DisconnectedTypes where

open import SpartanMLTT
open import Two-Properties
open import NaturalNumbers-Properties
open import DiscreteAndSeparated
open import UF-Retracts
open import UF-Equiv

disconnected₀ : 𝓤 ̇ → 𝓤 ̇
disconnected₀ X = retract 𝟚 of X

disconnected₁ : 𝓤 ̇ → 𝓤 ̇
disconnected₁ X = Σ p ꞉ (X → 𝟚) , fiber p ₀ × fiber p ₁

disconnected₂ : 𝓤 ̇ → 𝓤 ⁺ ̇
disconnected₂ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)

disconnected₃ : 𝓤 ̇ → 𝓤 ⁺ ̇
disconnected₃ {𝓤} X = Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X)

disconnected-eq : (X : 𝓤 ̇ )
                → (disconnected₀ X → disconnected₁ X)
                × (disconnected₁ X → disconnected₂ X)
                × (disconnected₂ X → disconnected₃ X)
                × (disconnected₃ X → disconnected₀ X)

disconnected-eq {𝓤} X = (f , g , h , k)
 where
  f : (Σ p ꞉ (X → 𝟚) , Σ s ꞉ (𝟚 → X) , p ∘ s ∼ id)
    → Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ≡ ₀) × (Σ x ꞉ X , p x ≡ ₁)
  f (p , s , e) = p , (s ₀ , e ₀) , (s ₁ , e ₁)

  g : (Σ p ꞉ (X → 𝟚) , (Σ x ꞉ X , p x ≡ ₀) × (Σ x ꞉ X , p x ≡ ₁))
    → Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁)
  g (p , (x₀ , e₀) , (x₁ , e₁)) = (Σ x ꞉ X , p x ≡ ₀) ,
                                  (Σ x ꞉ X , p x ≡ ₁) ,
                                  (x₀ , e₀) ,
                                  (x₁ , e₁) ,
                                  qinveq ϕ (γ , γϕ , ϕγ)
   where
    ϕ : X → (Σ x ꞉ X , p x ≡ ₀) + (Σ x ꞉ X , p x ≡ ₁)
    ϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ≡ ₀) → inl (x , r₀))
           (λ (r₁ : p x ≡ ₁) → inr (x , r₁))

    γ : (Σ x ꞉ X , p x ≡ ₀) + (Σ x ꞉ X , p x ≡ ₁) → X
    γ (inl (x , r₀)) = x
    γ (inr (x , r₁)) = x

    ϕγ : ϕ ∘ γ ∼ id
    ϕγ (inl (x , r₀)) = 𝟚-equality-cases₀ r₀
    ϕγ (inr (x , r₁)) = 𝟚-equality-cases₁ r₁

    γϕ : γ ∘ ϕ ∼ id
    γϕ x = 𝟚-equality-cases
           (λ (r₀ : p x ≡ ₀) → ap γ (𝟚-equality-cases₀ r₀))
           (λ (r₁ : p x ≡ ₁) → ap γ (𝟚-equality-cases₁ r₁))

  h : (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (X ≃ X₀ + X₁))
    → (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X))
  h (X₀ , X₁ , x₀ , x₁ , (γ , (ϕ , γϕ) , _)) = (X₀ , X₁ , x₀ , x₁ , (γ , ϕ , γϕ))

  k : (Σ X₀ ꞉ 𝓤 ̇ , Σ X₁ ꞉ 𝓤 ̇ , X₀ × X₁ × (retract (X₀ + X₁) of X))
    → Σ p ꞉ (X → 𝟚) , Σ s ꞉ (𝟚 → X) , p ∘ s ∼ id
  k (X₀ , X₁ , x₀ , x₁ , (γ , ϕ , γϕ)) = p , s , ps
   where
    p : X → 𝟚
    p x = Cases (γ x) (λ _ → ₀) (λ _ → ₁)

    s : 𝟚 → X
    s ₀ = ϕ (inl x₀)
    s ₁ = ϕ (inr x₁)

    ps : p ∘ s ∼ id
    ps ₀ = ap (cases (λ _ → ₀) (λ _ → ₁)) (γϕ (inl x₀))
    ps ₁ = ap (cases (λ _ → ₀) (λ _ → ₁)) (γϕ (inr x₁))

\end{code}

The following is our official notion of disconnectedness (logically
equivalent to the other ones):

\begin{code}

disconnected : 𝓤 ̇ → 𝓤 ̇
disconnected = disconnected₀

\end{code}

Some examples:

\begin{code}

𝟚-disconnected : disconnected 𝟚
𝟚-disconnected = identity-retraction

ℕ-disconnected : disconnected ℕ
ℕ-disconnected = (r , s , rs)
 where
  r : ℕ → 𝟚
  r zero     = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = zero
  s ₁ = succ zero

  rs : (n : 𝟚) → r (s n) ≡ n
  rs ₀ = refl
  rs ₁ = refl

non-trivial-with-isolated-point-gives-disconnected : {Y : 𝓥 ̇ }
                                                   → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , (y₀ ≢ y₁) × is-isolated y₀ )
                                                   → disconnected Y
non-trivial-with-isolated-point-gives-disconnected (y₀ , y₁ , ne , i) =
  𝟚-retract-of-non-trivial-type-with-isolated-point ne i

non-trivial-discrete-gives-disconnected : {Y : 𝓥 ̇ }
                                        → (Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≢ y₁)
                                        → is-discrete Y
                                        → disconnected Y
non-trivial-discrete-gives-disconnected (y₀ , y₁ , ne) d =
  non-trivial-with-isolated-point-gives-disconnected (y₀ , y₁ , ne , d y₀)


ℕ-disconnected' : disconnected ℕ
ℕ-disconnected' = non-trivial-discrete-gives-disconnected (0 , 1 , succ-no-fp 0) ℕ-is-discrete

disconnected-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → retract X of Y
                     → disconnected X
                     → disconnected Y
disconnected-retract = retracts-compose

\end{code}

TODO. Define totally disconnected. Then maybe for compact types the
notions of total disconnectedness and total separatedness agree.
