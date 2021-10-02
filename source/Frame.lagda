Ayberk Tosun, 8 March 2021.

Ported from `ayberkt/formal-topology-in-UF`.

 * Frames.
 * Frame homomorphisms.

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚)
open import UF-Base
open import UF-PropTrunc
open import UF-FunExt
open import UF-PropTrunc

module Frame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF-Subsingletons
open import UF-Subsingleton-Combinators
open import UF-Subsingletons-FunExt

open AllCombinators pt fe

\end{code}

\section{Preliminaries}

By Fam_𝓤(A), we denote the type of families on type A with index types
living in universe 𝓤.

\begin{code}

private
  variable
    𝓤′ 𝓥′ 𝓦′ : Universe

Fam : (𝓤 : Universe) → 𝓥 ̇ → 𝓤 ⁺ ⊔ 𝓥 ̇
Fam 𝓤 A = Σ I ꞉ (𝓤 ̇) , (I → A)

fmap-syntax : {A : 𝓤 ̇} {B : 𝓥 ̇}
            → (A → B) → Fam 𝓦 A → Fam 𝓦 B
fmap-syntax h (I , f) = I , h ∘ f

infix 2 fmap-syntax

syntax fmap-syntax (λ x → e) U = ⁅ e ∣ x ε U ⁆

compr-syntax : {A : 𝓤 ̇} (I : 𝓦 ̇) → (I → A) → Fam 𝓦 A
compr-syntax I f = I , f

infix 2 compr-syntax

syntax compr-syntax I (λ x → e) = ⁅ e ∣ x ∶ I ⁆

\end{code}

We define two projections for families: (1) for the index type,
and (2) for the enumeration function.

\begin{code}

index : {A : 𝓤 ̇} → Fam 𝓥 A → 𝓥 ̇
index (I , _) = I

_[_] : {A : 𝓤 ̇} → (U : Fam 𝓥 A) → index U → A
(_ , f) [ i ] = f i

infixr 9 _[_]

\end{code}

We define some order-theoretic notions that are also defined in the
`Dcpo` module. Ideally, this should be factored out into a standalone
module to be imported by both this module and the `Dcpo` module.

\begin{code}

is-reflexive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-reflexive {A = A} _≤_ = Ɐ x ∶ A , x ≤ x

is-transitive : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-transitive {A = A} _≤_ =
 Ɐ x ∶ A , Ɐ y ∶ A , Ɐ z ∶ A , x ≤ y ⇒ y ≤ z ⇒ x ≤ z

is-preorder : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
is-preorder {A = A} _≤_ = is-reflexive _≤_ ∧ is-transitive _≤_

\end{code}

Antisymmetry is not propositional unless A is a set. We will always
work with sets but the fact they are sets will be a corollary of their
equipment with an antisymmetric order so they are not sets a priori.

\begin{code}

is-antisymmetric : {A : 𝓤 ̇} → (A → A → Ω 𝓥) → (𝓤 ⊔ 𝓥) ̇
is-antisymmetric {A = A} _≤_ = {x y : A} → (x ≤ y) holds → (y ≤ x) holds → x ≡ y

being-antisymmetric-is-prop : {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥)
                            → is-set A
                            → is-prop (is-antisymmetric _≤_)
being-antisymmetric-is-prop {𝓤} {A} _≤_ A-is-set =
 Π-is-prop' fe (λ x → Π-is-prop' fe (λ y → Π₂-is-prop fe (λ _ _ → A-is-set {x} {y})))

is-partial-order : (A : 𝓤 ̇) → (A → A → Ω 𝓥) → 𝓤 ⊔ 𝓥 ̇
is-partial-order A _≤_ = is-preorder _≤_ holds ×  is-antisymmetric _≤_

being-partial-order-is-prop : (A : 𝓤 ̇) (_≤_ : A → A → Ω 𝓥)
                            → is-prop (is-partial-order A _≤_)
being-partial-order-is-prop A _≤_ = prop-criterion γ
 where
  γ : is-partial-order A _≤_ → is-prop (is-partial-order A _≤_)
  γ (p , a) = ×-is-prop
               (holds-is-prop (is-preorder _≤_))
               (being-antisymmetric-is-prop _≤_ i)
   where
    i : is-set A
    i = type-with-prop-valued-refl-antisym-rel-is-set
         (λ x y → (x ≤ y) holds)
         (λ x y → holds-is-prop (x ≤ y))
         (pr₁ p)
         (λ x y → a {x} {y})

\end{code}

\section{Definition of poset}

A (𝓤, 𝓥)-poset is a poset whose

  - carrier lives in universe 𝓤, and
  - whose relation lives in universe 𝓥.

\begin{code}

poset-structure : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ̇
poset-structure 𝓥 A =
 Σ _≤_ ꞉ (A → A → Ω 𝓥) , (is-partial-order A _≤_)

poset : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
poset 𝓤 𝓥 = Σ A ꞉ 𝓤 ̇ , poset-structure 𝓥 A

∣_∣ₚ : poset 𝓤 𝓥 → 𝓤 ̇
∣ A , _ ∣ₚ = A

rel-syntax : (P : poset 𝓤 𝓥)  → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
rel-syntax (_ , _≤_ , _) = _≤_

syntax rel-syntax P x y = x ≤[ P ] y

poset-eq-syntax : (P : poset 𝓤 𝓥) → ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
poset-eq-syntax P x y = x ≤[ P ] y ∧ y ≤[ P ] x

syntax poset-eq-syntax P x y = x ≣[ P ] y

≤-is-reflexive : (P : poset 𝓤 𝓥)
               → is-reflexive (λ x y → x ≤[ P ] x) holds
≤-is-reflexive (_ , _ , ((r , _) , _)) = r

reflexivity+ : (P : poset 𝓤 𝓥)
             → {x y : pr₁ P} → x ≡ y → (x ≤[ P ] y) holds
reflexivity+ P {x} {y} p =
 transport (λ - → (x ≤[ P ] -) holds) p (≤-is-reflexive P x)

≤-is-transitive : (P : poset 𝓤 𝓥)
                → is-transitive (λ x y → x ≤[ P ] y) holds
≤-is-transitive (_ , _ , ((_ , t) , _)) = t

≤-is-antisymmetric : (P : poset 𝓤 𝓥)
                   → is-antisymmetric (λ x y → x ≤[ P ] y)
≤-is-antisymmetric (_ , _ , (_ , a)) = a

carrier-of-[_]-is-set : (P : poset 𝓤 𝓥) → is-set ∣ P ∣ₚ
carrier-of-[_]-is-set P@ (A , _)=
 type-with-prop-valued-refl-antisym-rel-is-set
  (λ x y → (x ≤[ P ] y) holds)
  (λ x y → holds-is-prop (x ≤[ P ] y))
  (≤-is-reflexive P)
  (λ x y → ≤-is-antisymmetric P {x} {y})

\end{code}

Some convenient syntax for reasoning with posets.

\begin{code}

module PosetNotation (P : poset 𝓤 𝓥) where

 _≤_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
 x ≤ y = x ≤[ P ] y

 infix 4 _≤_

 _≣_ : ∣ P ∣ₚ → ∣ P ∣ₚ → Ω 𝓥
 x ≣ y = x ≣[ P ] y

module PosetReasoning (P : poset 𝓤 𝓥) where

 open PosetNotation P using (_≤_)

 _≤⟨_⟩_ : (x : ∣ P ∣ₚ) {y z : ∣ P ∣ₚ}
        → (x ≤ y) holds → (y ≤ z) holds → (x ≤ z) holds
 x ≤⟨ p ⟩ q = ≤-is-transitive P _ _ _ p q

 _■ : (x : ∣ P ∣ₚ) → (x ≤ x) holds
 _■ = ≤-is-reflexive P

 infixr 0 _≤⟨_⟩_
 infix  1 _■

infix 1 _≡[_]≡_

_≡[_]≡_ : {A : 𝓤 ̇} → A → is-set A → A → Ω 𝓤
x ≡[ iss ]≡ y = (x ≡ y) , iss

\end{code}

\section{Meets}

\begin{code}

module Meets {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 is-top : A → Ω (𝓤 ⊔ 𝓥)
 is-top t = Ɐ x ∶ A , (x ≤ t)

 _is-a-lower-bound-of_ : A → A × A → Ω 𝓥
 l is-a-lower-bound-of (x , y) = (l ≤ x) ∧ (l ≤ y)

 lower-bound : A × A → 𝓤 ⊔ 𝓥 ̇
 lower-bound (x , y) =
   Σ l ꞉ A , (l is-a-lower-bound-of (x , y)) holds

 _is-glb-of_ : A → A × A → Ω (𝓤 ⊔ 𝓥)
 l is-glb-of (x , y) = l is-a-lower-bound-of (x , y)
                     ∧ (Ɐ (l′ , _) ∶ lower-bound (x , y) , (l′ ≤ l))

\end{code}

\section{Joins}

\begin{code}

module Joins {A : 𝓤 ̇} (_≤_ : A → A → Ω 𝓥) where

 _is-an-upper-bound-of_ : A → Fam 𝓦 A → Ω (𝓥 ⊔ 𝓦)
 u is-an-upper-bound-of U = Ɐ i ∶ index U , (U [ i ]) ≤ u

 upper-bound : Fam 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 upper-bound U = Σ u ꞉ A , (u is-an-upper-bound-of U) holds

 _is-lub-of_ : A → Fam 𝓦 A → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
 u is-lub-of U = (u is-an-upper-bound-of U)
               ∧ (Ɐ (u′ , _) ∶ upper-bound U , (u ≤ u′))

module JoinNotation {A : 𝓤 ̇} (⋁_ : Fam 𝓦 A → A) where

 join-syntax : (I : 𝓦 ̇) → (I → A) → A
 join-syntax I f = ⋁ (I , f)

 ⋁⟨⟩-syntax : {I : 𝓦 ̇} → (I → A) → A
 ⋁⟨⟩-syntax {I = I} f = join-syntax I f

 infix 2 join-syntax
 infix 2 ⋁⟨⟩-syntax

 syntax join-syntax I (λ i → e) = ⋁⟨ i ∶ I ⟩ e
 syntax ⋁⟨⟩-syntax    (λ i → e) = ⋁⟨ i ⟩ e

\end{code}

\section{Definition of frame}

A (𝓤, 𝓥, 𝓦)-frame is a frame whose

  - carrier lives in universe 𝓤,
  - order lives in universe 𝓥, and
  - index types live in universe 𝓦.

\begin{code}

frame-data : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-data 𝓥 𝓦 A = (A → A → Ω 𝓥)   -- order
                 × A               -- top element
                 × (A → A → A)     -- binary meets
                 × (Fam 𝓦 A → A)   -- arbitrary joins

satisfies-frame-laws : {A : 𝓤 ̇} → frame-data 𝓥 𝓦 A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
satisfies-frame-laws {𝓤 = 𝓤} {𝓥} {𝓦} {A = A}  (_≤_ , 𝟏 , _⊓_ , ⊔_) =
 Σ p ꞉ is-partial-order A _≤_ , rest p holds
 where
  open Meets _≤_
  open Joins _≤_
  open JoinNotation ⊔_

  rest : is-partial-order A _≤_ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
  rest p = β ∧ γ ∧ δ ∧ ε
   where
    P : poset 𝓤 𝓥
    P = A , _≤_ , p

    iss : is-set A
    iss = carrier-of-[ P ]-is-set

    β = is-top 𝟏
    γ = Ɐ (x , y) ∶ (A × A) , ((x ⊓ y) is-glb-of (x , y))
    δ = Ɐ U ∶ Fam 𝓦 A , (⊔ U) is-lub-of U
    ε = Ɐ (x , U) ∶ A × Fam 𝓦 A ,
        (x ⊓ (⋁⟨ i ⟩ U [ i ]) ≡[ iss ]≡ ⋁⟨ i ⟩ x ⊓ (U [ i ]))

frame-structure : (𝓥 𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame-structure 𝓥 𝓦 A =
  Σ d ꞉ (frame-data 𝓥 𝓦 A) , satisfies-frame-laws d

\end{code}

The type of (𝓤, 𝓥, 𝓦)-frames is then defined as:

\begin{code}

frame : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
frame 𝓤 𝓥 𝓦 = Σ A ꞉ (𝓤 ̇) , frame-structure 𝓥 𝓦 A

\end{code}

The underlying poset of a frame:

\begin{code}

poset-of : frame 𝓤 𝓥 𝓦 → poset 𝓤 𝓥
poset-of (A , (_≤_ , _ , _ , _) , p , _) = A , _≤_ , p

\end{code}

Some projections.

\begin{code}

⟨_⟩ : frame 𝓤 𝓥 𝓦 → 𝓤 ̇
⟨ (A , (_≤_ , _ , _ , _) , p , _) ⟩ = A

𝟏[_] : (F : frame 𝓤 𝓥 𝓦) →  ⟨ F ⟩
𝟏[ (A , (_ , 𝟏 , _ , _) , p , _) ] = 𝟏

𝟏-is-top : (F : frame 𝓤 𝓥 𝓦) → (x : ⟨ F ⟩) → (x ≤[ poset-of F ] 𝟏[ F ]) holds
𝟏-is-top (A , _ , _ , p , _) = p

meet-of : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
meet-of (_ , (_ , _ , _∧_ , _) , _ , _) x y = x ∧ y

infix 4 meet-of

syntax meet-of F x y = x ∧[ F ] y

join-of : (F : frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → ⟨ F ⟩
join-of (_ , (_ , _ , _ , ⋁_) , _ , _) = ⋁_

infix 3 join-of

syntax join-of F U = ⋁[ F ] U

\end{code}

\begin{code}

∧[_]-lower₁ : (A : frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
            → ((x ∧[ A ] y) ≤[ poset-of A ] x) holds
∧[_]-lower₁ (A , _ , _ , (_ , γ , _ , _)) x y = pr₁ (pr₁ (γ (x , y)))

∧[_]-lower₂ : (A : frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
            → ((x ∧[ A ] y) ≤[ poset-of A ] y) holds
∧[_]-lower₂ (A , _ , _ , (_ , γ , _ , _)) x y = pr₂ (pr₁ (γ (x , y)))

∧[_]-greatest : (A : frame 𝓤 𝓥 𝓦) (x y : ⟨ A ⟩)
              → (z : ⟨ A ⟩)
              → (z ≤[ poset-of A ] x) holds
              → (z ≤[ poset-of A ] y) holds
              → (z ≤[ poset-of A ] (x ∧[ A ] y)) holds
∧[_]-greatest (A , _ , _ , (_ , γ , _ , _)) x y z p q =
  pr₂ (γ (x , y)) (z , p , q)

\end{code}

\begin{code}

⋁[_]-upper : (A : frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 ⟨ A ⟩) (i : index U)
        → ((U [ i ]) ≤[ poset-of A ] (⋁[ A ] U)) holds
⋁[_]-upper (A , _ , _ , (_ , _ , c , _)) U i = pr₁ (c U) i

⋁[_]-least : (A : frame 𝓤 𝓥 𝓦) → (U : Fam 𝓦 ⟨ A ⟩)
           → let open Joins (λ x y → x ≤[ poset-of A ] y)
             in ((u , _) : upper-bound U) → ((⋁[ A ] U) ≤[ poset-of A ] u) holds
⋁[_]-least (A , _ , _ , (_ , _ , c , _)) U = pr₂ (c U)

\end{code}

\begin{code}

𝟚 : (𝓤 : Universe) → 𝓤 ̇
𝟚 𝓤 = 𝟙 {𝓤} + 𝟙 {𝓤}

binary-join : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩ → ⟨ F ⟩ → ⟨ F ⟩
binary-join {𝓦 = 𝓦} F x y = ⋁[ F ] 𝟚 𝓦 , α
  where
  α : 𝟚 𝓦 → ⟨ F ⟩
  α (inl *) = x
  α (inr *) = y

infix 3 binary-join
syntax binary-join F x y = x ∨[ F ] y

\end{code}

\begin{code}

𝟎[_] : (F : frame 𝓤 𝓥 𝓦) → ⟨ F ⟩
𝟎[ F ] = ⋁[ F ] 𝟘 , λ ()

𝟎-is-bottom : (F : frame 𝓤 𝓥 𝓦)
            → (x : ⟨ F ⟩) → (𝟎[ F ] ≤[ poset-of F ] x) holds
𝟎-is-bottom F x = ⋁[ F ]-least (𝟘 , λ ()) (x , λ ())

\end{code}

\begin{code}

distributivity : (F : frame 𝓤 𝓥 𝓦)
               → (x : ⟨ F ⟩)
               → (U : Fam 𝓦 ⟨ F ⟩)
               → let open JoinNotation (λ - → ⋁[ F ] -) in
                 x ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))
               ≡ ⋁⟨ i ⟩ (x ∧[ F ] (U [ i ]))
distributivity (_ , _ , _ , (_ , _ , _ , d)) x U = d (x , U)

\end{code}

\section{Frame homomorphisms}

\begin{code}

is-a-frame-homomorphism : (F : frame 𝓤  𝓥  𝓦)
                          (G : frame 𝓤′ 𝓥′ 𝓦′)
                        → (⟨ F ⟩ → ⟨ G ⟩)
                        → Ω (𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′)
is-a-frame-homomorphism {𝓦 = 𝓦} F G f = α ∧ β ∧ γ
 where
  P = poset-of G

  iss : is-set ⟨ G ⟩
  iss = carrier-of-[ P ]-is-set

  open Joins (λ x y → x ≤[ P ] y)

  α = f 𝟏[ F ] ≡[ iss ]≡ 𝟏[ G ]
  β = Ɐ (x , y) ∶ ⟨ F ⟩ × ⟨ F ⟩ , (f (x ∧[ F ] y) ≡[ iss ]≡ f x ∧[ G ] f y)
  γ = Ɐ U ∶ Fam 𝓦 ⟨ F ⟩ , f (⋁[ F ] U) is-lub-of ⁅ f x ∣ x ε U ⁆

_─f→_ : frame 𝓤 𝓥 𝓦 → frame 𝓤′ 𝓥′ 𝓦′ → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓤′ ⊔ 𝓥′ ̇
F ─f→ G =
 Σ f ꞉ (⟨ F ⟩ → ⟨ G ⟩) , is-a-frame-homomorphism F G f holds

is-monotonic : (P : poset 𝓤 𝓥) (Q : poset 𝓤′ 𝓥′)
             → (pr₁ P → pr₁ Q) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓥′)
is-monotonic P Q f =
 Ɐ (x , y) ∶ (pr₁ P × pr₁ P) , ((x ≤[ P ] y) ⇒ f x ≤[ Q ] f y)

\end{code}

\section{Some properties of frames}

\begin{code}

∧[_]-unique : (F : frame 𝓤 𝓥 𝓦) {x y z : ⟨ F ⟩}
            → let open Meets (λ x y → x ≤[ poset-of F ] y) in
              (z is-glb-of (x , y)) holds → z ≡ (x ∧[ F ] y)
∧[ F ]-unique {x} {y} {z} (p , q) = ≤-is-antisymmetric (poset-of F) β γ
 where
  β : (z ≤[ poset-of F ] (x ∧[ F ] y)) holds
  β = ∧[ F ]-greatest x y z (pr₁ p) (pr₂ p)

  γ : ((x ∧[ F ] y) ≤[ poset-of F ] z) holds
  γ = q ((x ∧[ F ] y) , ∧[ F ]-lower₁ x y , ∧[ F ]-lower₂ x y)

\end{code}

\begin{code}

⋁[_]-unique : (F : frame 𝓤 𝓥 𝓦) (U : Fam 𝓦 ⟨ F ⟩) (u : ⟨ F ⟩)
         → let open Joins (λ x y → x ≤[ poset-of F ] y) in
           (u is-lub-of U) holds → u ≡ ⋁[ F ] U
⋁[_]-unique F U u (p , q) = ≤-is-antisymmetric (poset-of F) γ β
 where
  open PosetNotation (poset-of F)

  γ : (u ≤ (⋁[ F ] U)) holds
  γ = q ((⋁[ F ] U) , ⋁[ F ]-upper U)

  β : ((⋁[ F ] U) ≤ u) holds
  β = ⋁[ F ]-least U (u , p)

connecting-lemma₁ : (F : frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                  → (x ≤[ poset-of F ] y) holds
                  → x ≡ x ∧[ F ] y
connecting-lemma₁ F x y p = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)

  β : (x is-a-lower-bound-of (x , y)) holds
  β = ≤-is-reflexive (poset-of F) x , p

  γ : (Ɐ (z , _) ∶ lower-bound (x , y) , z ≤[ poset-of F ] x) holds
  γ (z , q , _) = q

frame-morphisms-are-monotonic : (F : frame 𝓤  𝓥  𝓦)
                                (G : frame 𝓤′ 𝓥′ 𝓦′)
                              → (f : ⟨ F ⟩ → ⟨ G ⟩)
                              → is-a-frame-homomorphism F G f holds
                              → is-monotonic (poset-of F) (poset-of G) f holds
frame-morphisms-are-monotonic F G f (_ , ψ , _) (x , y) p =
 f x            ≤⟨ i                         ⟩
 f (x ∧[ F ] y) ≤⟨ ii                        ⟩
 f x ∧[ G ] f y ≤⟨ ∧[ G ]-lower₂ (f x) (f y) ⟩
 f y            ■
  where
   open PosetReasoning (poset-of G)

   i  = reflexivity+ (poset-of G) (ap f (connecting-lemma₁ F x y p))
   ii = reflexivity+ (poset-of G) (ψ (x , y))


\end{code}

\begin{code}

∧[_]-is-commutative : (F : frame 𝓤 𝓥 𝓦) (x y : ⟨ F ⟩)
                 → x ∧[ F ] y ≡ y ∧[ F ] x
∧[ F ]-is-commutative x y = ∧[ F ]-unique (β , γ)
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)
  open PosetNotation (poset-of F) using (_≤_)

  β : ((x ∧[ F ] y) is-a-lower-bound-of (y , x)) holds
  β = (∧[ F ]-lower₂ x y) , (∧[ F ]-lower₁ x y)

  γ : (Ɐ (l , _) ∶ lower-bound (y , x) , l ≤ (x ∧[ F ] y)) holds
  γ (l , p , q) = ∧[ F ]-greatest x y l q p

\end{code}

\begin{code}

⋁[_]-iterated-join : (F : frame 𝓤 𝓥 𝓦) (I : 𝓦 ̇) (J : I → 𝓦 ̇)
                → (f : (i : I) → J i → ⟨ F ⟩)
                → ⋁[ F ] ((Σ i ꞉ I , J i) , uncurry f)
                ≡ ⋁[ F ] ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆
⋁[ F ]-iterated-join I J f = ⋁[ F ]-unique _ _ (β , γ)
 where
  open Joins (λ x y → x ≤[ poset-of F ] y)
  open PosetReasoning (poset-of F) renaming (_■ to _QED)

  β : ((⋁[ F ] (Σ J , uncurry f))
      is-an-upper-bound-of
      ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆) holds
  β i = ⋁[ F ]-least _ (_ , λ jᵢ → ⋁[ F ]-upper _ (i , jᵢ))

  γ : (Ɐ (u , _) ∶ upper-bound ⁅ ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ∣ i ∶ I ⁆ ,
       (⋁[ F ] (Σ J , uncurry f)) ≤[ poset-of F ] _ ) holds
  γ (u , p) = ⋁[ F ]-least (Σ J , uncurry f) (_ , δ)
   where
    δ : (u is-an-upper-bound-of (Σ J , uncurry f)) holds
    δ  (i , j) = f i j                      ≤⟨ ⋁[ F ]-upper _ j ⟩
                 ⋁[ F ] ⁅ f i j ∣ j ∶ J i ⁆ ≤⟨ p i              ⟩
                 u                          QED

\end{code}

\begin{code}

∧[_]-is-idempotent : (F : frame 𝓤 𝓥 𝓦)
                   → (x : ⟨ F ⟩) → x ≡ x ∧[ F ] x
∧[ F ]-is-idempotent x = ≤-is-antisymmetric (poset-of F) β γ
 where
  α : (x ≤[ poset-of F ] x) holds
  α = ≤-is-reflexive (poset-of F) x

  β : (x ≤[ poset-of F ] (x ∧[ F ] x)) holds
  β = ∧[ F ]-greatest x x x α α

  γ : ((x ∧[ F ] x) ≤[ poset-of F ] x) holds
  γ = ∧[ F ]-lower₁ x x

\end{code}

\begin{code}

distributivity+ : (F : frame 𝓤 𝓥 𝓦)
                → let open JoinNotation (λ - → ⋁[ F ] -) in
                  (U@(I , _) V@(J , _) : Fam 𝓦 ⟨ F ⟩)
                → (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))
                ≡ (⋁⟨ (i , j) ∶ (I × J)  ⟩ ((U [ i ]) ∧[ F ] (V [ j ])))
distributivity+ F U@(I , _) V@(J , _) =
 (⋁⟨ i ⟩ (U [ i ])) ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))     ≡⟨ i   ⟩
 (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (⋁⟨ i ⟩ (U [ i ]))     ≡⟨ ii  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (V [ j ])) ∧[ F ] (U [ i ]))     ≡⟨ iii ⟩
 (⋁⟨ i ⟩ (U [ i ] ∧[ F ] (⋁⟨ j ⟩ (V [ j ]))))     ≡⟨ iv  ⟩
 (⋁⟨ i ⟩ (⋁⟨ j ⟩ (U [ i ] ∧[ F ] V [ j ])))       ≡⟨ v   ⟩
 (⋁⟨ (i , j) ∶ I × J  ⟩ (U [ i ] ∧[ F ] V [ j ])) ∎
 where
  open JoinNotation (λ - → ⋁[ F ] -)

  i   = ∧[ F ]-is-commutative (⋁⟨ i ⟩ (U [ i ])) (⋁⟨ j ⟩ (V [ j ]))
  ii  = distributivity F (⋁⟨ j ⟩ (V [ j ])) U
  iii = ap
         (λ - → ⋁[ F ] (I , -))
         (dfunext fe λ i → ∧[ F ]-is-commutative (⋁⟨ j ⟩ V [ j ]) (U [ i ]))
  iv  = ap
         (λ - → join-of F (I , -))
         (dfunext fe λ i → distributivity F (U [ i ]) V)
  v   = ⋁[ F ]-iterated-join I (λ _ → J) (λ i j → U [ i ] ∧[ F ] V [ j ]) ⁻¹

\end{code}
