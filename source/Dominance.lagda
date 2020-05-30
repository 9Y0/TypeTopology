Martin Escardo, January 2018, May 2020

Based on joint work with Cory Knapp.
http://www.cs.bham.ac.uk/~mhe/papers/partial-elements-and-recursion.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Equiv
open import UF-Subsingletons hiding (⊤)
open import UF-Subsingletons-FunExt
open import UF-FunExt

module Dominance (𝓤 : Universe) (fe : FunExt) where

𝓤⁺ = 𝓤 ⁺

D2 : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤⁺ ̇
D2 d = (X : 𝓤 ̇ ) → is-prop(d X)

D3 : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤⁺ ̇
D3 d = (X : 𝓤 ̇ ) → d X → is-prop X

D4 : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤 ̇
D4 d = d 𝟙

D5 : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤⁺ ̇
D5 d = (P : 𝓤 ̇ ) (Q : P → 𝓤 ̇ ) → d P → ((p : P) → d(Q p)) → d(Σ Q)

\end{code}

condition D5 is more conceptual and often what we need in practice,
and condition D5' below is easier to check:

\begin{code}

D5' : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤⁺ ̇
D5' d = (P Q' : 𝓤 ̇ ) → d P → (P → d Q') → d(P × Q')

D5-gives-D5' : (d : 𝓤 ̇ → 𝓤 ̇ ) → D5 d → D5' d
D5-gives-D5' d d5 P Q' i j = d5 P (λ p → Q') i j

D3-and-D5'-give-D5 : propext 𝓤
                   → (d : 𝓤 ̇ → 𝓤 ̇ )
                   → D3 d
                   → D5' d
                   → D5 d
D3-and-D5'-give-D5 pe d d3 d5' P Q i j = w
 where
  Q' : 𝓤 ̇
  Q' = Σ Q
  k : is-prop P
  k = d3 P i
  l : (p : P) → is-prop (Q p)
  l p = d3 (Q p) (j p)
  m : is-prop Q'
  m = Σ-is-prop k l
  n : (p : P) → Q p ≡ Q'
  n p = pe (l p) m (λ q        → (p , q))
                   (λ (p' , q) → transport Q (k p' p) q)
  j' : P → d Q'
  j' p = transport d (n p) (j p)
  u : d (P × Q')
  u = d5' P Q' i j'
  v : P × Q' ≡ Σ Q
  v = pe (×-is-prop k m) m (λ (p , p' , q) → (p' , q))
                           (λ (p' , q)     → (p' , p' , q))
  w : d (Σ Q)
  w = transport d v u

is-dominance : (𝓤 ̇ → 𝓤 ̇ ) → 𝓤⁺ ̇
is-dominance d = D2 d × D3 d × D4 d × D5 d

Dominance : 𝓤⁺ ̇
Dominance = Σ is-dominance

is-dominant : (D : Dominance) → 𝓤 ̇ → 𝓤 ̇
is-dominant (d , _) = d

being-dominant-is-prop : (D : Dominance) → (X : 𝓤 ̇ ) → is-prop (is-dominant D X)
being-dominant-is-prop (_ , (isp , _)) = isp

dominant-types-are-props : (D : Dominance) → (X : 𝓤 ̇ ) → is-dominant D X → is-prop X
dominant-types-are-props (_ , (_ , (disp , _))) = disp

𝟙-is-dominant : (D : Dominance) → is-dominant D 𝟙
𝟙-is-dominant (_ , (_ , (_ , (oisd , _)))) = oisd

dominant-closed-under-Σ : (D : Dominance) → (P : 𝓤 ̇ ) (Q : P → 𝓤 ̇ )
                        → is-dominant D P → ((p : P) → is-dominant D (Q p)) → is-dominant D (Σ Q)
dominant-closed-under-Σ (_ , (_ , (_ , (_ , cus)))) = cus

being-dominance-is-prop : (d : 𝓤 ̇ → 𝓤 ̇ ) → is-prop (is-dominance d)
being-dominance-is-prop d = prop-criterion lemma
 where
  lemma : is-dominance d → is-prop (is-dominance d)
  lemma isd = Σ-is-prop
               (Π-is-prop (fe 𝓤⁺ 𝓤) λ _ → being-prop-is-prop (fe 𝓤 𝓤))
               λ _ → Σ-is-prop
                       (Π-is-prop (fe 𝓤⁺ 𝓤)
                          λ _ → Π-is-prop (fe 𝓤 𝓤)
                                   λ _ → being-prop-is-prop (fe 𝓤 𝓤))
                       λ _ → Σ-is-prop
                               (being-dominant-is-prop (d , isd) 𝟙)
                               λ _ → Π-is-prop (fe 𝓤⁺ 𝓤⁺)
                                        λ _ → Π-is-prop (fe 𝓤⁺ 𝓤)
                                                 λ Q → Π-is-prop (fe 𝓤 𝓤)
                                                          λ _ → Π-is-prop (fe 𝓤 𝓤)
                                                                   λ _ → being-dominant-is-prop (d , isd) (Σ Q)


\end{code}

Example: the decidable propositions form a dominance.

\begin{code}

module DecidableDominance where

 open import DecidableAndDetachable

 decidable-dominance : Dominance
 decidable-dominance = (λ P → is-prop P × decidable P) ,
                       (λ P → Σ-is-prop
                                 (being-prop-is-prop (fe 𝓤 𝓤))
                                 (decidability-of-prop-is-prop (fe 𝓤 𝓤₀))) ,
                       (λ X → pr₁) ,
                       (𝟙-is-prop , inl *) ,
                       λ P Q dP dQ → Σ-is-prop (pr₁ dP) (λ p → pr₁(dQ p)) ,
                                      decidable-closed-under-Σ (pr₁ dP) (pr₂ dP) λ p → pr₂ (dQ p)

module lift (d : 𝓤 ̇ → 𝓤 ̇ ) (isd : is-dominance d) where

 D : Dominance
 D = (d , isd)

 L : ∀ {𝓥} (X : 𝓥 ̇ ) → 𝓤⁺ ⊔ 𝓥 ̇
 L X = Σ P ꞉ 𝓤 ̇ , d P × (P → X)

 LL : ∀ {𝓥} (X : 𝓥 ̇ ) → 𝓤⁺ ⊔ 𝓥 ̇
 LL X = L(L X)

 _⇀_ : ∀ {𝓥 𝓦} → 𝓥 ̇ → 𝓦 ̇ → 𝓤⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
 X ⇀ Y = X → L Y

 isDefined : ∀ {𝓥} {X : 𝓥 ̇ } → L X → 𝓤 ̇
 isDefined (P , (isdp , φ)) = P

 is-dominantisDefined : ∀ {𝓥} {X : 𝓥 ̇ } → (x̃ : L X) → is-dominant D (isDefined x̃)
 is-dominantisDefined (P , (isdp , φ)) = isdp

 value : ∀ {𝓥} {X : 𝓥 ̇ } → (x̃ : L X) → isDefined x̃ → X
 value (P , (isdp , φ)) = φ

 η : ∀ {𝓥} {X : 𝓥 ̇ } → X → L X
 η x = 𝟙 , 𝟙-is-dominant D , λ _ → x

 extension : ∀ {𝓥 𝓦} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X ⇀ Y) → (L X → L Y)
 extension {𝓥} {𝓦} {X} {Y} f (P , (isdp , φ)) = (Q , (isdq , γ))
  where
   Q : 𝓤 ̇
   Q = Σ p ꞉ P , isDefined(f(φ p))

   isdq : is-dominant D Q
   isdq = dominant-closed-under-Σ D
            P
            (λ p → isDefined(f(φ p)))
            isdp
            (λ p → is-dominantisDefined (f (φ p)))

   γ : Q → Y
   γ (p , def) = value(f (φ p)) def

 _♯ : ∀ {𝓥 𝓦} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X ⇀ Y) → (L X → L Y)
 f ♯ = extension f

 _◌_ : ∀ {𝓥 𝓦 𝓣} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ }
     → (Y ⇀ Z) → (X ⇀ Y) → (X ⇀ Z)
 g ◌ f = g ♯ ∘ f

 μ : ∀ {𝓥} {X : 𝓥 ̇ } → L(L X) → L X
 μ = extension id

 {- TODO:
 kleisli-law₀ : ∀ {𝓥} {X : 𝓥 ̇ } → extension (η {𝓥} {X}) ∼ id
 kleisli-law₀ {𝓥} {X} (P , (isdp , φ)) = {!!}

 kleisli-law₁ : ∀ {𝓥 𝓦)} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } (f : X ⇀ Y) → extension f ∘ η ∼ f
 kleisli-law₁ {𝓥} {𝓦} {X} {Y} f x = {!!}


 kleisli-law₂ : ∀ {𝓥 𝓦) T} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ } (f : X ⇀ Y) (g : Y ⇀ Z)
              → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
 kleisli-law₂ {𝓥} {𝓦} {𝓣} {X} {Y} {Z} f g (P , (isdp , φ)) = {!!}
 -}

\end{code}
