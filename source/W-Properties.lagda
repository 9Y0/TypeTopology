Martin Escardo, 19th December 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module W-Properties where

open import SpartanMLTT
open import W
open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-FunExt

W-≡-fold : funext 𝓥 (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           {x  : X} {f  : A x  → W A}
           {x' : X} {f' : A x' → W A}
         → Σ p ꞉ x ≡ x' , ((a : A x) → f a ≡ f' (transport A p a))
         → sup x f ≡[ W A ] sup x' f'
W-≡-fold fe {X} {A} {x} {f} {.x} {f'} (refl , ϕ) = ap (sup x) (dfunext fe ϕ)


W-is-prop : funext 𝓥 (𝓤 ⊔ 𝓥)
          → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → is-prop X
          → is-prop (W A)
W-is-prop fe {X} {A} X-is-prop (sup x f) (sup x' f') = γ
 where
  p : x ≡ x'
  p = X-is-prop x x'

  IH : (a : A x) → f a ≡ f' (transport A p a)
  IH a = W-is-prop fe X-is-prop (f a) (f' (transport A p a))

  γ : sup x f ≡ sup x' f'
  γ = W-≡-fold fe (p , IH)


W-≡-unfold : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             {x  : X} {f  : A x  → W A}
             {x' : X} {f' : A x' → W A}
           → sup x f ≡[ W A ] sup x' f'
           → Σ p ꞉ x ≡ x' , ((a : A x) → f a ≡ f' (transport A p a))
W-≡-unfold {𝓤} {𝓥} {X} {A} {x} {f} {x} {f} refl = refl , (λ a → refl)


W-≡-fold-unfold : (fe : funext 𝓥 (𝓤 ⊔ 𝓥))
                  {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                  {x  : X} {f  : A x  → W A}
                  {x' : X} {f' : A x' → W A}
                → (q : sup x f ≡[ W A ] sup x' f')
                → W-≡-fold fe (W-≡-unfold q) ≡ q
W-≡-fold-unfold fe {X} {A} {x} {f} {.x} {.f} refl = γ
 where
  γ : ap (sup x) (dfunext fe (λ x → refl)) ≡ refl
  γ = ap (ap (sup x)) (dfunext-refl fe f)


W-is-set : funext 𝓥 (𝓤 ⊔ 𝓥)
         → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → is-set X
         → is-set (W A)
W-is-set fe {X} {A} i {sup x f} {sup x' f'} = γ
 where
  S = Σ p ꞉ x ≡ x' , ((a : A x) → f a ≡ f' (transport A p a))

  α : is-prop S
  α = Σ-is-prop i (λ p → Π-is-prop fe λ a → W-is-set fe i)

  β : retract (sup x f ≡ sup x' f') of S
  β = W-≡-fold fe , W-≡-unfold , (W-≡-fold-unfold fe)

  γ : is-prop (sup x f ≡ sup x' f')
  γ = retract-of-prop β α

\end{code}
