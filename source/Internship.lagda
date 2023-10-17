\begin{code}
{-# OPTIONS --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.FunExt
open import UF.Subsingletons

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
open import Categories.Category fe

module _ {𝓤 : Universe} -- where lifted type lives
         (A : 𝓤 ̇ )
         (𝓦 : Universe) -- where the carrier lives
         (𝓣 : Universe) -- where the truth values live
        where

 is-bot : {X : 𝓦 ̇ } → (X → X → 𝓣 ̇ ) → X → 𝓦 ⊔ 𝓣 ̇
 is-bot {X} _⊑_ x = {y : X} → x ⊑ y

 DPartAxioms : {X : 𝓦 ̇ } (_⊑_ : X → X → 𝓣 ̇ ) (⊥ : X)
               (∐ : ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X))
             → 𝓥 ⁺ ⊔ 𝓦 ⊔ 𝓣 ̇ 
 DPartAxioms {X} _⊑_ ⊥ ∐ =
  PosetAxioms.poset-axioms _⊑_ ×
  is-bot _⊑_ ⊥ × 
  ({I : 𝓥 ̇ } (α : I → X) (p : is-directed _⊑_ α) → is-sup _⊑_ (∐ (α , p)) α)

 DPartOb : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺ ̇
 DPartOb =
  Σ X ꞉ 𝓦 ̇ ,
  Σ _⊑_ ꞉ (X → X → 𝓣 ̇ ) ,
  Σ ⊥ ꞉ X ,
  Σ η ꞉ (A → X) ,
  Σ ∐ ꞉ ({I : 𝓥 ̇ } → (Σ α ꞉ (I → X) , is-directed _⊑_ α) → X) ,
   (DPartAxioms _⊑_ ⊥ ∐)

 DPartHom : DPartOb → DPartOb → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
 DPartHom (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , _) (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , _) =
  Σ f ꞉ (X → H) ,
  Σ f⊑ ꞉ ({x1 x2 : X} → x1 ⊑ₓ x2 → f x1 ⊑ₕ f x2) ,
   (f ⊥ₓ ＝ ⊥ₕ) ×
   (f ∘ ηₓ ＝ ηₕ) ×
   ({I : 𝓥 ̇ } (α : I → X) (p : is-directed _⊑ₓ_ α) →
    is-sup _⊑ₕ_ (f (∐ₓ (α , p))) (f ∘ α))

 DPartHom-is-set : {X Y : DPartOb} → is-set (DPartHom X Y)
 DPartHom-is-set {X} {Y} =
  Σ-is-set
   (Π-is-set fe (λ _ → {!   !})) -- This follows from the PosetAxioms on Y, probably need some projection functions...
   λ f → Σ-is-set {! Π-is-set !} {!   !}

 DPartId : (X : DPartOb) → DPartHom X X
 DPartId (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , _ , _ , ∐ₓ-is-sup) =
  id , id , refl , refl , ∐ₓ-is-sup

 DPartComp : (X H S : DPartOb) → DPartHom X H → DPartHom H S → DPartHom X S
 DPartComp
  (X , _⊑ₓ_ , ⊥ₓ , ηₓ , ∐ₓ , paₓ , _ , ∐ₓ-is-sup)
  (H , _⊑ₕ_ , ⊥ₕ , ηₕ , ∐ₕ , paₕ , _ , ∐ₕ-is-sup)
  (S , _⊑ₛ_ , ⊥ₛ , ηₛ , ∐ₛ , paₛ , _ , ∐ₛ-is-sup)
  (g , g⊑ , g⊥ , gη , g∐)
  (f , f⊑ , f⊥ , fη , f∐) =
   f ∘ g ,
   f⊑ ∘ g⊑ ,
   (ap f g⊥ ∙ f⊥) ,
   (ap (f ∘_) gη ∙ fη) ,
   ∘∐
   where
    ∘∐ : {I : 𝓥 ̇} (α : I → X) (p : is-directed _⊑ₓ_ α)
       → is-sup _⊑ₛ_ (f (g (∐ₓ (α , p)))) (f ∘ g ∘ α)
    ∘∐ α p = {! ∐ₛ-is-sup !}
     where
      test2 : g (∐ₓ (α , p)) ＝ ∐ₕ (g ∘ α , _)
      test2 = sups-are-unique _⊑ₕ_ paₕ (g ∘ α)
               (g∐ α p)
               (∐ₕ-is-sup (g ∘ α)
                (inhabited-if-directed _⊑ₓ_ _ p ,
                λ i j → ∥∥-functor (λ (k , αᵢ⊑αₖ , αⱼ⊑αₖ) → k , g⊑ αᵢ⊑αₖ , g⊑ αⱼ⊑αₖ) (semidirected-if-directed _⊑ₓ_ _ p i j)))

      test : f (g (∐ₓ (α , p))) ＝ ∐ₛ (f ∘ g ∘ α , {!   !})
      test = (ap f test2) ∙ {!   !}

 DPartPre : precategory (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓣 ⁺) (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓦 ⊔ 𝓣)
 DPartPre =
  make
   (DPartOb , DPartHom , DPartId , DPartComp)
   {!   !}

data _⊥ (A : 𝓤 ̇ ) : 𝓥 ⁺ ⊔ 𝓤 ̇
data Leq (A : 𝓤 ̇ ) : A ⊥ → A ⊥ → 𝓥 ⁺ ⊔ 𝓤 ̇ 

data _⊥ A where
 incl : A → A ⊥
 bot : A ⊥
 lub : {I : 𝓥 ̇ } → (Σ α ꞉ (I → A ⊥) , is-directed (Leq A) α) → A ⊥

data Leq A where
 refl : ∀ {x} → Leq A x x
 trans : ∀ {x y z} → Leq A x y → Leq A y z → Leq A x z
 bot-leq : ∀ {x} → Leq A bot x
 lub-upperbound : {I : 𝓥 ̇ } {α : I → A ⊥} (p : is-directed (Leq A) α)
                  (i : I) → Leq A (α i) (lub (α , p))
 lub-lowest : {I : 𝓥 ̇ } {α : I → A ⊥} (p : is-directed (Leq A) α) {x : A ⊥}
            → ((i : I) → Leq A (α i) x)
            → Leq A (lub (α , p)) x

-- FIXME: This is very close to the x ⊑⟨ 𝓓 ⟩ y syntax of DCPOs, probably not a good idea...
syntax Leq A x y = x ⊑[ A ] y

lift-is-DPart : (A : 𝓤 ̇ ) → DPartOb A (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
lift-is-DPart A = A ⊥ , Leq A , bot , incl , lub , {!   !}

postulate
 -- We have to postulate this, as we cannot define a QIIT
 anti-sym : {A : 𝓤 ̇ } {x y : A ⊥} → x ⊑[ A ] y → y ⊑[ A ] x → x ＝ y

 -- TODO: Elimination principle for A ⊥, Leq A, we probably need more category theory for that


\end{code}  