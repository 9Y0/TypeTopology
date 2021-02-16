Martin Escardo, 15 February 2021.

Ongoing joint work with Marc Bezem, Thierry Coquand, and Peter Dybjer.

For the moment this file is not for public consumption, but it is
publicly visible.

At the moment this file is a mess in many respects. It will be tidied
up soon. But at least we have proved the desired result.

  For any universe 𝓤, there is a group in the successor universe 𝓤⁺
  which is not isomorphic to any group in 𝓤.

Of course, in the other direction, any group in 𝓤 has an isomorphic
copy in 𝓤⁺, so the above says that there are strictly more groups in
𝓤⁺ than in 𝓤.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons
open import UF-Univalence
open import UF-UA-FunExt

module OrdinalsFreeGroup
        (pt : propositional-truncations-exist)
        (ua : Univalence)
       where

open import SpartanMLTT
open import Groups
open import FreeGroup
open import OrdinalsType hiding (⟨_⟩)
open import OrdinalOfOrdinals
open import UF-Embeddings
open import UF-Univalence

fe : Fun-Ext
fe {𝓤} {𝓥} = Univalence-gives-FunExt ua 𝓤 𝓥

pe : Prop-Ext
pe {𝓤} = univalence-gives-propext (ua 𝓤)

open FreeGroupInterface pt fe pe

OFG : (𝓤 : Universe) → Group (𝓤 ⁺⁺)
OFG 𝓤 = free-group (Ordinal 𝓤)

ηOFG : (𝓤 : Universe) → Ordinal 𝓤 → ⟨ OFG 𝓤 ⟩
ηOFG 𝓤 = η-free-group (Ordinal 𝓤)

ηOFG-is-embedding : Univalence → is-embedding (ηOFG 𝓤)
ηOFG-is-embedding {𝓤} ua = η-free-group-is-embedding (Ordinal 𝓤) (type-of-ordinals-is-set ua)

module _ {𝓤 : Universe} where

 A = Ordinal 𝓤

 A-is-set : is-set A
 A-is-set = type-of-ordinals-is-set ua

 open free-group-construction A
 open import List
 open import UF-Base

 _≡[X]_ : X → X → 𝓤 ̇
 (m , a) ≡[X] (n , b) = (m ≡ n) × (a ≃ₒ b)

 from-≡[X] : {x y : X} → x ≡[X] y → x ≡ y
 from-≡[X] {m , a} {n , b} (p , q) = to-×-≡ p (eqtoidₒ ua a b q)

 to-≡[X] : {x y : X} → x ≡ y → x ≡[X] y
 to-≡[X] {m , a} {m , a} refl = refl , ≃ₒ-refl a

 _≡[FA]_ : FA → FA → 𝓤 ̇
 []      ≡[FA] []      = 𝟙
 []      ≡[FA] (y ∷ t) = 𝟘
 (x ∷ s) ≡[FA] []      = 𝟘
 (x ∷ s) ≡[FA] (y ∷ t) = (x ≡[X] y) × (s ≡[FA] t)

 from-≡[FA] : {s t : FA} → s ≡[FA] t → s ≡ t
 from-≡[FA] {[]}    {[]}    e       = refl
 from-≡[FA] {x ∷ s} {y ∷ t} (p , q) = ap₂ _∷_ (from-≡[X] p) (from-≡[FA] q)

 to-≡[FA] : {s t : FA} → s ≡ t → s ≡[FA] t
 to-≡[FA] {[]} {[]}       p = *
 to-≡[FA] {x ∷ s} {y ∷ t} p = to-≡[X]  (equal-heads p) ,
                              to-≡[FA] (equal-tails p)

 _▶_ : FA → FA → 𝓤 ̇
 []          ▶ t = 𝟘
 (x ∷ [])    ▶ t = 𝟘
 (x ∷ y ∷ s) ▶ t = (y ≡[X] (x ⁻)) × (s ≡[FA] t)

 _◗_ : FA → FA → 𝓤 ̇
 []      ◗ t       = 𝟘
 (x ∷ s) ◗ []      = (x ∷ s) ▶ []
 (x ∷ s) ◗ (y ∷ t) = ((x ∷ s) ▶ (y ∷ t)) + (x ≡[X] y × (s ◗ t))

 ◗-lemma : (x y : X) (s : List X) → y ≡ (x ⁻) → (x ∷ y ∷ s) ◗ s
 ◗-lemma x _ []      refl = to-≡[X] {x ⁻} refl , *
 ◗-lemma x _ (z ∷ s) refl = inl (to-≡[X]  {x ⁻} refl ,
                                 to-≡[X]  {z}   refl ,
                                 to-≡[FA] {s}   refl)

 ◗-gives-▷ : {s t : FA} → s ◗ t → s ▷ t
 ◗-gives-▷ {[]} {t} r = 𝟘-elim r
 ◗-gives-▷ {x ∷ y ∷ s} {[]} (p , q) = [] , s , x ,
                                    ap (λ - → x ∷ - ∷ s) (from-≡[X] p) ,
                                    ((from-≡[FA] q)⁻¹)
 ◗-gives-▷ {x ∷ y ∷ s} {z ∷ t} (inl (p , q)) = γ (from-≡[X] p)
                                                 (from-≡[FA] q)
  where
   γ : y ≡ x ⁻ → s ≡ z ∷ t → x ∷ y ∷ s ▷ z ∷ t
   γ p q = [] , s , x , ap (λ - → x ∷ (- ∷ s)) p , (q ⁻¹)
 ◗-gives-▷ {x ∷ s} {y ∷ t} (inr (p , r)) = γ (from-≡[X] p) IH
  where
   IH : s ▷ t
   IH = ◗-gives-▷ r

   γ : x ≡ y → s ▷ t → (x ∷ s) ▷ (y ∷ t)
   γ refl = ∷-▷ x

 ▷-gives-◗ : {s t : FA} → s ▷ t → s ◗ t
 ▷-gives-◗ (u , v , x , refl , refl) = f u v x
  where
   f : (u v : FA) (x : X) → (u ++ [ x ] ++ [ x ⁻ ] ++ v) ◗ (u ++ v)
   f []      []      x = to-≡[X] {x ⁻} refl , *
   f []      (y ∷ v) x = inl (to-≡[X] {x ⁻} refl , to-≡[X] {y} refl , to-≡[FA] {v} refl)
   f (y ∷ u) v       x = inr (to-≡[X] {y} refl , f u v x)

 redex : FA → 𝓤 ̇
 redex []          = 𝟘
 redex (x ∷ [])    = 𝟘
 redex (x ∷ y ∷ s) = (y ≡[X] (x ⁻)) + redex (y ∷ s)

 reduct : (s : FA) → redex s → FA
 reduct (x ∷ y ∷ s) (inl p) = s
 reduct (x ∷ y ∷ s) (inr r) = x ∷ reduct (y ∷ s) r

 _◗[_]_ : FA → ℕ → FA → 𝓤 ̇
 s ◗[ 0 ]      t = s ≡[FA] t
 s ◗[ succ n ] t = Σ r ꞉ redex s , (reduct s r ◗[ n ] t)

 lemma-reduct→ : (s : FA) (r : redex s) →  s ◗ reduct s r
 lemma-reduct→ (x ∷ y ∷ s) (inl p) = ◗-lemma x y s (from-≡[X] p)
 lemma-reduct→ (x ∷ y ∷ s) (inr r) = inr (to-≡[X] {x} refl ,
                                         lemma-reduct→ (y ∷ s) r)


 lemma-reduct← : (s t : FA) → s ◗ t → Σ r ꞉ redex s , reduct s r ≡ t
 lemma-reduct← (x ∷ [])    (z ∷ t) (inl ())
 lemma-reduct← (x ∷ [])    (z ∷ t) (inr ())
 lemma-reduct← (x ∷ y ∷ s) []      (p , q)       = inl p , from-≡[FA] q
 lemma-reduct← (x ∷ y ∷ s) (z ∷ t) (inl (p , q)) = inl p , from-≡[FA] q
 lemma-reduct← (x ∷ y ∷ s) (z ∷ t) (inr (p , r)) = inr (pr₁ IH) ,
                                                   ap₂ _∷_ (from-≡[X] p) (pr₂ IH)
  where
   IH : Σ r ꞉ redex (y ∷ s) , reduct (y ∷ s) r ≡ t
   IH = lemma-reduct← (y ∷ s) t r


 redex-chain : ℕ → FA → 𝓤 ̇
 redex-chain 0        s = 𝟙
 redex-chain (succ n) s = Σ r ꞉ redex s , redex-chain n (reduct s r)

 chain-reduct : (s : FA) (n : ℕ) → redex-chain n s → FA
 chain-reduct s 0        ρ       = s
 chain-reduct s (succ n) (r , ρ) = chain-reduct (reduct s r) n ρ

 chain-lemma→ : (s : FA) (n : ℕ) (ρ : redex-chain n s) → s ▷[ n ] chain-reduct s n ρ
 chain-lemma→ s 0 ρ = refl
 chain-lemma→ s (succ n) (r , ρ) = reduct s r ,
                                   ◗-gives-▷ (lemma-reduct→ s r) ,
                                   chain-lemma→ (reduct s r) n ρ

 _≏_ : FA → FA → 𝓤 ̇
 s ≏ t = Σ m ꞉ ℕ ,
         Σ n ꞉ ℕ ,
         Σ ρ ꞉ redex-chain m s ,
         Σ σ ꞉ redex-chain n t , (chain-reduct s m ρ  ≡[FA] chain-reduct t n σ)


 ≏-gives-∿ : (s t : FA) → s ≏ t → s ∿ t
 ≏-gives-∿ s t (m , n , ρ , σ , p) = γ
  where
   a : s ▷* chain-reduct s m ρ
   a = m , chain-lemma→ s m ρ

   b : t ▷* chain-reduct t n σ
   b = n , chain-lemma→ t n σ

   c : Σ u ꞉ FA , (s ▷* u) × (t ▷* u)
   c = chain-reduct t n σ  , transport (s ▷*_) (from-≡[FA] p) a , b

   γ : s ∿ t
   γ = to-∿ s t c

 chain-lemma← : (s t : FA) (n : ℕ) → s ▷[ n ] t → Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ t
 chain-lemma← s t 0 r = * , r
 chain-lemma← s t (succ n) (u , b , c) = γ IH l
  where
   IH : Σ ρ ꞉ redex-chain n u , (chain-reduct u n ρ ≡ t)
   IH = chain-lemma← u t n c

   b' : s ◗ u
   b' = ▷-gives-◗ b

   l : Σ r ꞉ redex s , reduct s r ≡ u
   l = lemma-reduct← s u b'


   γ : type-of IH
     → type-of l
     → Σ ρ' ꞉ redex-chain (succ n) s , (chain-reduct s (succ n) ρ' ≡ t)
   γ (ρ , refl) (r , refl) = (r , ρ) , refl

 ∿-gives-≏ : (s t : FA) → s ∿ t → s ≏ t
 ∿-gives-≏ s t e = γ a
  where
   a : Σ u ꞉ FA , (s ▷* u) × (t ▷* u)
   a = from-∿ Church-Rosser s t e

   γ : type-of a → s ≏ t
   γ (u , (m , ρ) , (n , σ)) = δ b c
    where
     b : Σ ρ ꞉ redex-chain m s , chain-reduct s m ρ ≡ u
     b = chain-lemma← s u m ρ

     c : Σ σ ꞉ redex-chain n t , chain-reduct t n σ ≡ u
     c = chain-lemma← t u n σ

     δ : type-of b → type-of c → s ≏ t
     δ (ρ , p) (σ , q) = m , n , ρ , σ , to-≡[FA] (p ∙ q ⁻¹)

 open free-group-construction-step₁ pt

 _∥≏∥_ : FA → FA → 𝓤 ̇
 s ∥≏∥ t = ∥ s ≏ t ∥

 open import UF-Equiv

 ∿-is-logically-equivalent-to-∥≏∥ : (s t : FA) → s ∾ t ⇔ s ∥≏∥ t
 ∿-is-logically-equivalent-to-∥≏∥ s t = ∥∥-functor (∿-gives-≏ s t) ,
                                       ∥∥-functor (≏-gives-∿ s t)
 ∿-is-equivalent-to-∥≏∥ : (s t : FA) → (s ∾ t) ≃ (s ∥≏∥ t)
 ∿-is-equivalent-to-∥≏∥ s t = logically-equivalent-props-are-equivalent
                               ∥∥-is-prop
                               ∥∥-is-prop
                               (lr-implication (∿-is-logically-equivalent-to-∥≏∥ s t))
                               (rl-implication (∿-is-logically-equivalent-to-∥≏∥ s t))

 open import UF-Size
 open import UF-Quotient pt fe pe
 open import SRTclosure
 open free-group-construction-step₂ fe pe

 -∥≏∥- : EqRel {𝓤 ⁺} {𝓤} FA
 -∥≏∥- = _∥≏∥_ , is-equiv-rel-transport _∾_ _∥≏∥_ (λ s t → ∥∥-is-prop)
                 ∿-is-logically-equivalent-to-∥≏∥ ∾-is-equiv-rel
 FA/∥≏∥ : 𝓤 ⁺ ̇
 FA/∥≏∥ = FA / -∥≏∥-

 FA/∾-is-equivalent-to-FA/∥≏∥ : FA/∾ ≃ FA/∥≏∥
 FA/∾-is-equivalent-to-FA/∥≏∥ = quotients-equivalent FA -∾- -∥≏∥-
                                (λ {s} {t} → ∿-is-logically-equivalent-to-∥≏∥ s t)

 native-size-of-ordinals-free-group : type-of ⟨ free-group (Ordinal 𝓤) ⟩ ≡ (𝓤 ⁺⁺ ̇ )
 native-size-of-ordinals-free-group = refl

 resizing-ordinals-free-group : ⟨ free-group (Ordinal 𝓤) ⟩ has-size (𝓤 ⁺)
 resizing-ordinals-free-group = γ
  where
   γ : Σ F ꞉ 𝓤 ⁺ ̇ , F ≃ ⟨ free-group (Ordinal 𝓤) ⟩
   γ = FA/∥≏∥ , ≃-sym FA/∾-is-equivalent-to-FA/∥≏∥

 open import UF-EquivalenceExamples

 ηη-native-size : ηη Has-size (𝓤 ⁺⁺)
 ηη-native-size y = fiber ηη y , ≃-refl _

 ηη-is-medium : ηη Has-size (𝓤 ⁺)
 ηη-is-medium = /-induction -∾- (λ y → fiber ηη y has-size (𝓤 ⁺))
                (λ y → has-size-is-prop ua (fiber ηη y) (𝓤 ⁺)) γ
  where
   e : (a : A) (s : FA) → (η/∾ (η a) ≡ η/∾ s) ≃ (η a ∥≏∥ s)
   e a s = (η/∾ (η a) ≡ η/∾ s) ≃⟨ I ⟩
           (η a ∾ s)           ≃⟨ II ⟩
           (η a ∥≏∥ s)         ■
    where
     I = logically-equivalent-props-are-equivalent
            (quotient-is-set -∾-)
            ∥∥-is-prop
            η/∾--relates-identified-points
            η/∾-identifies-related-points
     II = ∿-is-equivalent-to-∥≏∥ (η a) s

   d : (s : FA) → fiber ηη (η/∾ s) ≃ (Σ a ꞉ A , η a ∥≏∥ s)
   d s = (Σ a ꞉ A , η/∾ (η a) ≡ η/∾ s) ≃⟨ Σ-cong (λ a → e a s) ⟩
         (Σ a ꞉ A , η a ∥≏∥ s) ■

   γ : (s : FA) → fiber ηη (η/∾ s) has-size (𝓤 ⁺)
   γ s = (Σ a ꞉ A , η a ∥≏∥ s) , ≃-sym (d s)
    where
     notice : 𝓤 ⁺⁺ ̇
     notice = fiber ηη (η/∾ s)

\end{code}

But the above is not small enough.

\begin{code}

 η/∥≏∥ : FA → FA/∥≏∥
 η/∥≏∥ = η/ -∥≏∥-

 ηη' : A → FA/∥≏∥
 ηη' = η/ -∥≏∥- ∘ η

 ηη'-native-size : ηη' Has-size (𝓤 ⁺)
 ηη'-native-size y = fiber ηη' y , ≃-refl _

\end{code}

The following doesn't do anything useful, but see the comment below:

\begin{code}

 is-generator : FA → 𝓤₀ ̇
 is-generator [] = 𝟘
 is-generator (x ∷ y ∷ s) = 𝟘
 is-generator ((₀ , a) ∷ []) = 𝟙
 is-generator ((₁ , a) ∷ []) = 𝟘

 generator-lemma→ : (s : FA) → is-generator s → (Σ a ꞉ A , η a ≡ s)
 generator-lemma→ [] ()
 generator-lemma→ (₀ , a ∷ []) * = a , refl
 generator-lemma→ (₁ , a ∷ []) ()
 generator-lemma→ (x ∷ y ∷ s) ()


 generator-lemma← : (s : FA) → (Σ a ꞉ A , η a ≡ s) → is-generator s
 generator-lemma← .(η a) (a , refl) = *

 η-is-generator : (a : A) → is-generator (η a)
 η-is-generator a = *

 is-gen : FA → 𝓤 ̇
 is-gen s = Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , is-generator (chain-reduct s n ρ)

 ppp : (s : FA) → is-prop (Σ a ꞉ A , η a ∾ s)
 ppp s (a , e) (a' , e') = to-subtype-≡ (λ x → ∥∥-is-prop)
                            (η-identifies-∾-related-points A-is-set
                              (psrt-transitive (η a) s (η a')
                                e (psrt-symmetric (η a') s e')))

 gen-lemma→ : (s : FA) → (Σ a ꞉ A , η a ∾ s) → ∥ is-gen s ∥
 gen-lemma→ s (a , e) = ∥∥-functor f e
  where
   f : η a ∿ s → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , is-generator (chain-reduct s n ρ)
   f e = γ (d c)
    where
     c : Σ u ꞉ FA , (η a ▷* u) × (s ▷* u)
     c = from-∿ Church-Rosser (η a) s e
     d : type-of c → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ η a
     d (u , r , r') = δ r''
      where
       p : η a ≡ u
       p = η-irreducible* r
       r'' : s  ▷* η a
       r'' = transport (s ▷*_) (p ⁻¹) r'
       δ : s  ▷* η a → Σ n ꞉ ℕ , Σ ρ ꞉ redex-chain n s , chain-reduct s n ρ ≡ η a
       δ (n , r''') = (n , chain-lemma← s (η a) n r''')
     γ : type-of (d c) → codomain f
     γ (n , ρ , p) = n , ρ , transport is-generator (p ⁻¹) (η-is-generator a)

 gen-lemma← : (s : FA) → ∥ is-gen s ∥ → (Σ a ꞉ A , η a ∾ s)
 gen-lemma← s = ∥∥-rec (ppp s) f
  where
   f : is-gen s → (Σ a ꞉ A , η a ∾ s)
   f (n , ρ , i) = IV III
    where
     I : s ▷[ n ] chain-reduct s n ρ
     I = chain-lemma→ s n ρ
     II : chain-reduct s n ρ ∾ s
     II = ∣ to-∿ (chain-reduct s n ρ) s (chain-reduct s n ρ , (0 , refl) , (n , I)) ∣
     III : Σ a ꞉ A , (η a ≡ chain-reduct s n ρ)
     III = generator-lemma→ (chain-reduct s n ρ) i
     IV : type-of III → Σ a ꞉ A , η a ∾ s
     IV (a , p) = a , transport (_∾ s) (p ⁻¹) II

 gen-lemma : (s : FA) → (Σ a ꞉ A , η a ∾ s) ≃ ∥ is-gen s ∥
 gen-lemma s = logically-equivalent-props-are-equivalent
                (ppp s)
                ∥∥-is-prop
                (gen-lemma→ s)
                (gen-lemma← s)

 ηη-is-small : ηη Has-size 𝓤
 ηη-is-small = /-induction -∾- (λ y → fiber ηη y has-size 𝓤)
                (λ y → has-size-is-prop ua (fiber ηη y) 𝓤) γ
  where
   e : (a : A) (s : FA) → (η/∾ (η a) ≡ η/∾ s) ≃ (η a ∾ s)
   e a s = (η/∾ (η a) ≡ η/∾ s) ≃⟨ I ⟩
           (η a ∾ s)           ■
    where
     I = logically-equivalent-props-are-equivalent
            (quotient-is-set -∾-)
            ∥∥-is-prop
            η/∾--relates-identified-points
            η/∾-identifies-related-points

   d : (s : FA) → fiber ηη (η/∾ s) ≃ ∥ is-gen s ∥
   d s = (Σ a ꞉ A , η/∾ (η a) ≡ η/∾ s) ≃⟨ Σ-cong (λ a → e a s) ⟩
         (Σ a ꞉ A , η a ∾ s) ≃⟨ gen-lemma s ⟩
         ∥ is-gen s ∥  ■

   γ : (s : FA) → fiber ηη (η/∾ s) has-size 𝓤
   γ s = ∥ is-gen s ∥ , ≃-sym (d s)
    where
     notice : 𝓤 ⁺⁺ ̇
     notice = fiber ηη (η/∾ s)

\end{code}

So we finally obtain our desired result:

\begin{code}

 recall₁ : type-of ⟨ free-group (Ordinal 𝓤) ⟩ ≡ (𝓤 ⁺⁺ ̇ )
 recall₁ = native-size-of-ordinals-free-group

 recall₂ : ⟨ free-group (Ordinal 𝓤) ⟩ has-size (𝓤 ⁺)
 recall₂ = resizing-ordinals-free-group

 desired-result : ¬ (⟨ free-group (Ordinal 𝓤) ⟩ has-size 𝓤)
 desired-result h = the-type-of-ordinals-is-large
                     (size-contravariance ηη ηη-is-small h)
  where
   open import BuraliForti ua

\end{code}

The remainder of this file has useless stuff, kept maybe for
discussion only, before we delete it. (There is also useless stuff
above to be deleted.)

\begin{code}

 ◗[]-gives-▷[] : (n : ℕ) (s t : FA) → s ◗[ n ] t → s ▷[ n ] t
 ◗[]-gives-▷[] 0        s t r       = from-≡[FA] r
 ◗[]-gives-▷[] (succ n) s t (r , ρ) = reduct s r ,
                                      ◗-gives-▷ (lemma-reduct→ s r) ,
                                      ◗[]-gives-▷[] n (reduct s r) t ρ

 ▷[]-gives-◗[] : (n : ℕ) (s t : FA) → s ▷[ n ] t → s ◗[ n ] t
 ▷[]-gives-◗[] 0        s t r           = to-≡[FA] r
 ▷[]-gives-◗[] (succ n) s t (u , b , c) = γ
  where
   b' : s ◗ u
   b' = ▷-gives-◗ b

   IH : u ◗[ n ] t
   IH = ▷[]-gives-◗[] n u t c

   l : Σ re ꞉ redex s , reduct s re ≡ u
   l = lemma-reduct← s u b'

   re : redex s
   re = pr₁ l

   IH' : reduct s re ◗[ n ] t
   IH' = transport (λ - → - ◗[ n ] t) ((pr₂ l)⁻¹) IH

   γ : s ◗[ succ n ] t
   γ = re , IH'

 _◗*_ : FA → FA → 𝓤 ̇
 s ◗* t = Σ n ꞉ ℕ , s ◗[ n ] t

 ◗*-gives-▷* : (s t : FA) → s ◗* t → s ▷* t
 ◗*-gives-▷* s t (n , r) = n , ◗[]-gives-▷[] n s t r

 ▷*-gives-◗* : (s t : FA) → s ▷* t → s ◗* t
 ▷*-gives-◗* s t (n , r) = n , ▷[]-gives-◗[] n s t r

\end{code}

The universe level gets too big with this approach:

\begin{code}

 _≍_ : FA → FA → 𝓤 ⁺ ̇
 s ≍ t = Σ u ꞉ FA , (s ◗* u) × (t ◗* u)

\end{code}
