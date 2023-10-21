References:

[1]: Thorsten Altenkirch, Nils Anders Danielsson, Nicolai Kraus:
     Partiality, Revisited - The Partiality Monad as a Quotient Inductive-Inductive Type.
     FoSSaCS 2017: 534-549
     https://arxiv.org/abs/1610.09254

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import MLTT.Spartan

open import UF.Base

open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

open import UF.Equiv

module Internship
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
        ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
infixr -1 _$_

open PropositionalTruncation pt

open import Posets.Poset fe

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.Pointed pt fe 𝓥 renaming (⊥ to least)

open import Categories.Category fe

module _ {𝓤 : Universe} -- where lifted type lives
         (A : 𝓤 ̇ )
         (𝓦 : Universe) -- where the carrier lives
         (𝓣 : Universe) -- where the truth values live
        where

\end{code}

A directed partiality algebra over A is a pointed DCPO 𝓓, together with an
inclusion A → ⟪ 𝓓 ⟫

\begin{code}

 record DPartOb : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇  where
  field
   𝓓 : DCPO⊥ {𝓦} {𝓣}
   η : A → ⟪ 𝓓 ⟫

 underlying-DCPO⊥ : DPartOb → DCPO⊥
 underlying-DCPO⊥ X = 𝓓
  where
   open DPartOb X

 DPartOb＝ : {X Y : DPartOb}
           → let module X = DPartOb X
                 module Y = DPartOb Y
          in (p : ⟪ X.𝓓 ⟫ ＝ ⟪ Y.𝓓 ⟫)
           → (λ y₁ y₂ → idtofun _ _ (p ⁻¹) y₁ ⊑⟪ X.𝓓 ⟫ idtofun _ _ (p ⁻¹) y₂) ＝ underlying-order⊥ Y.𝓓
           → idtofun _ _ p (least X.𝓓) ＝ (least Y.𝓓)
           → idtofun _ _ p ∘ X.η ＝ Y.η
           → X ＝ Y
 DPartOb＝ {X} {Y} refl refl refl refl = γ p q
  where
   module X = DPartOb X
   module Y = DPartOb Y

   p : ⊥-is-least X.𝓓 ＝ ⊥-is-least Y.𝓓
   p = Π-is-prop fe (prop-valuedness (X.𝓓 ⁻) _) _ _

   q : axioms-of-dcpo (X.𝓓 ⁻) ＝ axioms-of-dcpo (Y.𝓓 ⁻)
   q = dcpo-axioms-is-prop (underlying-order⊥ X.𝓓) _ _

   γ : ⊥-is-least X.𝓓 ＝ ⊥-is-least Y.𝓓
     → axioms-of-dcpo (X.𝓓 ⁻) ＝ axioms-of-dcpo (Y.𝓓 ⁻)
     → _ ＝ _
   γ refl refl = refl

\end{code}

DPartOb is equivalent to the Sigma type corresponding to the one given in [1].

\begin{code}

 DPartAxioms : {X : 𝓦 ̇ } (_⊑_ : X → X → 𝓣 ̇ ) (⊥ : X)
               (∐ : ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X))
             → 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇ 
 DPartAxioms {X} _⊑_ ⊥ ∐ =
  PosetAxioms.poset-axioms _⊑_ ×
  is-least _⊑_ ⊥ × 
  ({I : 𝓥 ̇ } {α : I → X} (p : is-directed _⊑_ α) → is-sup _⊑_ (∐ (α , p)) α)

 DPartOb' : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 DPartOb' =
  Σ X ꞉ 𝓦 ̇ ,
  Σ _⊑_ ꞉ (X → X → 𝓣 ̇ ) ,
  Σ ⊥ ꞉ X ,
  Σ η ꞉ (A → X) ,
  Σ ∐ ꞉ ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X) ,
   (DPartAxioms _⊑_ ⊥ ∐)

 DPartOb≃DPartOb' : DPartOb ≃ DPartOb'
 DPartOb≃DPartOb' = qinveq f (g , gf , fg)
  where
   f : DPartOb → DPartOb'
   f X = ⟪ 𝓓 ⟫ ,
         underlying-order⊥ 𝓓 ,
         least 𝓓 ,
         η ,
         (λ (α , p) → ∐ (𝓓 ⁻) p) ,
         pr₁ (axioms-of-dcpo (𝓓 ⁻)) ,
         ⊥-is-least 𝓓 ,
         ∐-is-sup (𝓓 ⁻)
    where
     open DPartOb X

   g : DPartOb' → DPartOb
   g (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , pa , ⊥ₓ-is-least , ∐ₓ-is-sup) =
    record { 𝓓 = 𝓓 , ⊥ₓ , ⊥ₓ-is-least ; η = ηₓ }
    where
     𝓓 : DCPO {𝓦} {𝓣}
     𝓓 = X , _⊑ₓ_ , pa , (λ I α p → ∐ₓ (α , p) , ∐ₓ-is-sup p)

   gf : g ∘ f ∼ id
   gf X = DPartOb＝ refl refl refl refl

   fg : f ∘ g ∼ id
   fg _ = refl

\end{code}

A morphism of partiality algebras over A, is a strict continuous map which
preserves the inclusions of A.

\begin{code}

 record DPartHom (X Y : DPartOb) : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇  where
  module X = DPartOb X
  module Y = DPartOb Y

  field
   f : DCPO⊥[ X.𝓓 , Y.𝓓 ]
   f-strict : [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ (least X.𝓓) ＝ least Y.𝓓
   f-η : [ X.𝓓 ⁻ , Y.𝓓 ⁻ ]⟨ f ⟩ ∘ X.η ＝ Y.η

 DPart[_,_]⟨_⟩ : (X Y : DPartOb)
               → let module X = DPartOb X
                     module Y = DPartOb Y
              in (f : DPartHom X Y) → ⟪ X.𝓓 ⟫ → ⟪ Y.𝓓 ⟫
 DPart[ X , Y ]⟨ f ⟩ = pr₁ f.f
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f

 continuity-of-DPartHom : (X Y : DPartOb) (f : DPartHom X Y)
                        → let module X = DPartOb X
                              module Y = DPartOb Y
                       in is-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) DPart[ X , Y ]⟨ f ⟩
 continuity-of-DPartHom X Y f = continuity-of-function (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f


 DPartHom＝ : {X Y : DPartOb} {f g : DPartHom X Y}
            → DPart[ X , Y ]⟨ f ⟩ ＝ DPart[ X , Y ]⟨ g ⟩
            → f ＝ g
 DPartHom＝ {X} {Y} {f} {g} refl = γ p q r
  where
   module X = DPartOb X
   module Y = DPartOb Y
   module f = DPartHom f
   module g = DPartHom g

   p : f.f ＝ g.f
   p = to-Σ-＝
        (refl ,
         being-continuous-is-prop (X.𝓓 ⁻) (Y.𝓓 ⁻)
          (DPart[ X , Y ]⟨ f ⟩) _ _)

   q : f.f-strict ＝ g.f-strict
   q = sethood (Y.𝓓 ⁻) _ _

   r : f.f-η ＝ g.f-η
   r = Π-is-set fe (λ _ → sethood (Y.𝓓 ⁻)) _ _

   -- FIXME: Cannot match p as refl fsr
   γ : f.f ＝ g.f
     → f.f-strict ＝ g.f-strict
     → f.f-η ＝ g.f-η
     → _ ＝ _
   γ p refl refl = {! p !}

\end{code}

DPartHom is equivalent to the Sigma type corresponding to the one given in [1].
We use this to prove that DPartHom is a set.

\begin{code}

 image-is-directed-if-monotone : {I : 𝓥 ̇ } {X H : 𝓦 ̇ } {α : I → X} {f : X → H}
                               → (_⊑ₓ_ : X → X → 𝓣 ̇ ) (_⊑ₕ_ : H → H → 𝓣 ̇ )
                               → (f⊑ : (x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂)
                               → (p : is-directed _⊑ₓ_ α)
                               → is-directed _⊑ₕ_ (f ∘ α)
 image-is-directed-if-monotone {α = α} _⊑ₓ_ _⊑ₕ_ f⊑ p =
  inhabited-if-directed _⊑ₓ_ α p ,
  λ i j → ∥∥-functor
           (λ (k , αᵢ⊑αₖ , αⱼ⊑αₖ) → k , f⊑ _ _ αᵢ⊑αₖ , f⊑ _ _ αⱼ⊑αₖ)
           (semidirected-if-directed _⊑ₓ_ α p i j)

 DPartHom' : DPartOb' → DPartOb' → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 DPartHom' (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , _) (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , _) =
  Σ f ꞉ (X → H) ,
  Σ f⊑ ꞉ ((x₁ x₂ : X) → x₁ ⊑ₓ x₂ → f x₁ ⊑ₕ f x₂) ,
   (f ⊥ₓ ＝ ⊥ₕ) ×
   (f ∘ ηₓ ＝ ηₕ) ×
   ({I : 𝓥 ̇ } (α : I → X) (p : is-directed _⊑ₓ_ α) →
    f (∐ₓ (α , p)) ＝ ∐ₕ (f ∘ α , image-is-directed-if-monotone _⊑ₓ_ _⊑ₕ_ f⊑ p))

 DPartHom≃DPartHom' : (X Y : DPartOb)
                    → DPartHom X Y
                    ≃ DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
 DPartHom≃DPartHom' X Y = qinveq ψ (ϕ , ϕψ , ψϕ)
  where
   module X = DPartOb X
   module Y = DPartOb Y

   ψ : DPartHom X Y → DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y)
   ψ f = DPart[ X , Y ]⟨ f ⟩ ,
         monotone-if-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f ,
         f.f-strict ,
         f.f-η ,
         γ
    where
     module f = DPartHom f
    
     γ : {I : 𝓥 ̇ } (α : I → ⟪ X.𝓓 ⟫) (p : is-Directed (X.𝓓 ⁻) α)
       → DPart[ X , Y ]⟨ f ⟩ (∐ (X.𝓓 ⁻) p)
       ＝ ∐ (Y.𝓓 ⁻) (image-is-directed' (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f p)
     γ α p = continuous-∐-＝ (X.𝓓 ⁻) (Y.𝓓 ⁻) f.f p

   ϕ : DPartHom' (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y) → DPartHom X Y
   ϕ (f , f⊑ , f⊥ , fη , f∐) =
    record
     { f = f ,
           λ I α δ →
            transport⁻¹ (λ y → is-sup (underlying-order⊥ Y.𝓓) y (f ∘ α))
             (f∐ α δ)
             (∐-is-sup (Y.𝓓 ⁻) _)
     ; f-strict = f⊥
     ; f-η = fη }

   ϕψ : ϕ ∘ ψ ∼ id
   ϕψ f = DPartHom＝ refl
    where
     module f = DPartHom f

   -- FIXME: Simplifying this expression takes pretty long
   ψϕ : ψ ∘ ϕ ∼ id
   ψϕ f = {!   !}

 DPartHom'-is-set : (X H : DPartOb') → is-set (DPartHom' X H)
 DPartHom'-is-set (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , paₓ , ⊥ₓ-is-least , ∐ₓ-is-sup)
                  (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , paₕ , ⊥ₕ-is-least , ∐ₕ-is-sup) =
  Σ-is-set
   (Π-is-set fe (λ _ → H-is-set))
   λ f →
    props-are-sets
     (Σ-is-prop
      (Π₃-is-prop fe (λ x₁ x₂ x₁⊑x₂ → pr₁ (pr₂ paₕ) (f x₁) (f x₂)))
      λ f⊑ →
       ×₃-is-prop
        H-is-set
        (Π-is-set fe (λ _ → H-is-set))
        (Π-is-prop' fe (λ _ → Π₂-is-prop fe (λ _ _ → H-is-set))))
  where
   H-is-set : is-set H
   H-is-set = pr₁ paₕ

   ⊑ₕ-prop-valued : PosetAxioms.is-prop-valued _⊑ₕ_
   ⊑ₕ-prop-valued = pr₁ (pr₂ paₕ)

 DPartHom-is-set : (X Y : DPartOb) → is-set (DPartHom X Y)
 DPartHom-is-set X Y =
  equiv-to-set
   (DPartHom≃DPartHom' X Y)
   (DPartHom'-is-set (⌜ DPartOb≃DPartOb' ⌝ X) (⌜ DPartOb≃DPartOb' ⌝ Y))

\end{code}

\begin{code}

 DPartId : (X : DPartOb) → DPartHom X X
 DPartId X =
  record
   { f = id , λ I α → ∐-is-sup (𝓓 ⁻)
   ; f-strict = refl
   ; f-η = refl }
  where
   open DPartOb X

 DPartComp : (X Y Z : DPartOb) → DPartHom X Y → DPartHom Y Z → DPartHom X Z
 DPartComp X Y Z f g =
  record
   { f = DPart[ Y , Z ]⟨ g ⟩ ∘ DPart[ X , Y ]⟨ f ⟩ ,
         ∘-is-continuous (X.𝓓 ⁻) (Y.𝓓 ⁻) (Z.𝓓 ⁻)
          DPart[ X , Y ]⟨ f ⟩ DPart[ Y , Z ]⟨ g ⟩
          (continuity-of-DPartHom X Y f)
          (continuity-of-DPartHom Y Z g)
   ; f-strict = ap DPart[ Y , Z ]⟨ g ⟩ f.f-strict ∙ g.f-strict
   ; f-η = ap (DPart[ Y , Z ]⟨ g ⟩ ∘_) f.f-η ∙ g.f-η }
  where
   module f = DPartHom f
   module g = DPartHom g
   module X = DPartOb X
   module Y = DPartOb Y
   module Z = DPartOb Z

 DPartPre : precategory (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺) (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣)
 DPartPre =
  make
   (DPartOb , DPartHom , DPartId , DPartComp)
   (DPartHom-is-set ,
    (λ X Y f → DPartHom＝ refl) ,
    (λ X Y f → DPartHom＝ refl) ,
    λ X Y Z W f g h → DPartHom＝ refl)

\end{code}

We now consider the QIIT from [1] adapted to a DCPO setting.

\begin{code}

data _⊥ (A : 𝓤 ̇ ) : 𝓥 ⁺ ⊔ 𝓤 ̇
data Leq (A : 𝓤 ̇ ) : A ⊥ → A ⊥ → 𝓥 ⁺ ⊔ 𝓤 ̇ 

-- This definition gives a specified index k s.t. αᵢ ⊑ αₖ, αⱼ ⊑ αₖ instead of an
-- unspecified index k. Using this definition Leq A , A ⊥ become strictly
-- positive, but it's definitly not the definition we want.
wrong-is-directed : {I : 𝓥 ̇ } {X : 𝓦' ̇ } → (_⊑_ : X → X → 𝓣 ̇ ) → (I → X) → 𝓥 ⊔ 𝓣 ̇
wrong-is-directed {I = I} _⊑_ α =
 ∥ I ∥ ×
 ((i j : I) → Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))

data _⊥ A where
 incl : A → A ⊥
 bot : A ⊥
 lub : {I : 𝓥 ̇ } → (Σ α ꞉ (I → A ⊥) , wrong-is-directed (Leq A) α) → A ⊥

postulate
 ⊥-is-set : {A : 𝓤 ̇ } → is-set (A ⊥)

data Leq A where
 Leq-refl : (x : A ⊥) → Leq A x x
 Leq-trans : (x y z : A ⊥) → Leq A x y → Leq A y z → Leq A x z
 bot-leq : (x : A ⊥) → Leq A bot x
 lub-upperbound : {I : 𝓥 ̇ } {α : I → A ⊥} (p : wrong-is-directed (Leq A) α)
                  (i : I) → Leq A (α i) (lub (α , p))
 lub-lowest : {I : 𝓥 ̇ } {α : I → A ⊥} (p : wrong-is-directed (Leq A) α) {x : A ⊥}
            → ((i : I) → Leq A (α i) x)
            → Leq A (lub (α , p)) x

-- FIXME: This is very close to the x ⊑⟨ 𝓓 ⟩ y syntax of DCPOs, probably not a good idea...
syntax Leq A x y = x ⊑[ A ] y            

postulate
 Leq-is-prop-valued : {A : 𝓤 ̇ } (x y : A ⊥) → is-prop (x ⊑[ A ] y)
 Leq-anti-sym : {A : 𝓤 ̇ } (x y : A ⊥) → x ⊑[ A ] y → y ⊑[ A ] x → x ＝ y

 -- TODO: Elimination principle for A ⊥, Leq A, we probably need more category theory for that

lift-is-DPart : (A : 𝓤 ̇ ) → DPartOb A (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
lift-is-DPart A = record { 𝓓 = 𝓓 , bot , bot-leq ; η = incl }
 where
  pa : PosetAxioms.poset-axioms (Leq A)
  pa = ⊥-is-set , Leq-is-prop-valued , Leq-refl , Leq-trans , Leq-anti-sym

  -- FIXME: We cannot prove directed completeness, as we used the wrong notion
  -- of being directed.
  𝓓 : DCPO
  𝓓 = A ⊥ , Leq A , pa , {!   !}

\end{code}     