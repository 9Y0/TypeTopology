Tom de Jong 25th May 2019

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Subsingletons hiding (⊥)
open import UF-FunExt
open import UF-PropTrunc hiding (⊥)

module LiftingDcpo'
  (𝓣 : Universe) -- fix a universe for the propositions
  (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
  (pe : propext 𝓣)
  (pt : propositional-truncations-exist)
  where

open import UF-Base
open import Lifting 𝓣
open import LiftingSet 𝓣
open import Dcpos pt fe 𝓤₀
open PropositionalTruncation pt 
open import UF-ImageAndSurjection
open ImageAndSurjection pt
open import UF-Equiv
open import UF-Miscelanea
open import DiscreteAndSeparated

open import LiftingMonad 𝓣
open import LiftingIdentityViaSIP 𝓣
open import DcpoFunctionSpace pt fe 𝓤₀


\end{code}

We prefer to work with this version of the order.
We also develop some lemmas about it. This duplicates some material in
LiftingUnivalentPrecategory, as we do not want to assume univalence here.

Eventually, we should move this code to a more sensible place.
Perhaps LiftingUnivalentPrecategory.

\begin{code}
module _ 
  {𝓤 : Universe}
  (X : 𝓤 ̇)
  (s : is-set X)
  where

 open import LiftingUnivalentPrecategory 𝓣 X

 _⊑'_ : (l m : 𝓛 X) → 𝓤 ⊔ 𝓣 ⁺ ̇
 -- Note: this maps into a bigger universe than _⊑_ (!)
 l ⊑' m = is-defined l → l ≡ m

 ⊑-to-⊑' : {l m : 𝓛 X} → l ⊑ m → l ⊑' m
 ⊑-to-⊑' {l} {m} a d = ⊑-anti pe fe fe (a , b) where
  b : m ⊑ l
  b = c , v where
   c : is-defined m → is-defined l
   c = λ _ → d
   v : (e : is-defined m) → value m e ≡ value l d
   v e = value m e         ≡⟨ ap (value m)
                             (being-defined-is-a-prop m e (pr₁ a d)) ⟩
         value m (pr₁ a d) ≡⟨ g ⁻¹ ⟩
         value l d         ∎ where
    h : is-defined l → is-defined m
    h = pr₁ a
    g : value l d ≡ value m (pr₁ a d)
    g = pr₂ a d

 ⊑'-to-⊑ : {l m : 𝓛 X} → l ⊑' m → l ⊑ m
 ⊑'-to-⊑ {l} {m} a = back-eqtofun e g where
  e : (l ⊑ m) ≃ (is-defined l → l ⊑ m)
  e = ⊑-open fe fe fe l m
  g : is-defined l → l ⊑ m
  g d = transport (_⊑_ l) (a d) (𝓛-id l)
{-
 ⋍-to-≡ : {l m : 𝓛 X} → l ⋍ m → l ≡ m
 ⋍-to-≡ {l} {m} (deq , veq) = ⊑-anti pe fe fe (a , b)
  where
   a : l ⊑ m
   a = eqtofun deq , happly veq
   b : m ⊑ l
   b = (back-eqtofun deq , h)
    where
     h : (d : is-defined m) → value m d ≡ value l (back-eqtofun deq d)
     h d = value m d                                  ≡⟨ ap (value m) (being-defined-is-a-prop m d _) ⟩
           value m (eqtofun deq (back-eqtofun deq d)) ≡⟨ (happly veq (back-eqtofun deq d)) ⁻¹ ⟩
           value l (back-eqtofun deq d)               ∎
           -}

 -- Find a better home for this
 value-is-constant : {l : 𝓛 X} (d e : is-defined l) → value l d ≡ value l e
 value-is-constant {l} d e = ap (value l) (being-defined-is-a-prop l d e)

 is-defined-η-≡ : {l : 𝓛 X} (d : is-defined l) → l ≡ η (value l d)
 is-defined-η-≡ {l} d = ⊑-to-⊑' ((λ _ → *) , λ (e : is-defined l) → value-is-constant {l} e d) d
 --

 ⊑'-is-reflexive : is-reflexive (_⊑'_)
 ⊑'-is-reflexive l d = refl

 ⊑'-is-transitive : is-transitive (_⊑'_)
 ⊑'-is-transitive l m n a b d = l ≡⟨ a d ⟩
                                m ≡⟨ b (transport is-defined (a d) d) ⟩
                                n ∎

 ⊑'-is-antisymmetric : is-antisymmetric (_⊑'_)
 ⊑'-is-antisymmetric l m a b = ⊑-anti pe fe fe (⊑'-to-⊑ a , ⊑'-to-⊑ b)

 ⊑'-prop-valued : is-prop-valued (_⊑'_)
 ⊑'-prop-valued l _ = Π-is-prop fe λ (d : is-defined l) → lifting-of-set-is-a-set fe fe pe X s

 ≡-of-values-from-≡ : {l m : 𝓛 X} → l ≡ m
                    → {d : is-defined l}
                    → {e : is-defined m}
                    → value l d ≡ value m e
 ≡-of-values-from-≡ {l} refl {d} {e} = ap (value l) (being-defined-is-a-prop l d e)
 
 ≡-to-is-defined : {l m : 𝓛 X} → l ≡ m → is-defined l → is-defined m
 ≡-to-is-defined e d = transport is-defined e d

 family-value-map : {I : 𝓤₀ ̇}
                  → (α : I → 𝓛 X)
                  → Σ (\(i : I) → is-defined (α i)) → X
 family-value-map α (i , d) = value (α i) d

 directed-family-value-map-is-constant : {I : 𝓤₀ ̇}
                                       → (α : I → 𝓛 X)
                                       → (δ : is-directed _⊑'_ α )
                                       → constant (family-value-map α)
 directed-family-value-map-is-constant {I} α δ (i₀ , d₀) (i₁ , d₁) =
  γ (is-directed-order _⊑'_ α δ i₀ i₁) where
   f : Σ (λ i → is-defined (α i)) → X
   f = family-value-map α
   γ : ∃ (\(k : I) → (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
   γ = ∥∥-rec s g where
    g : Σ (\(k : I) → (α i₀ ⊑' α k) × (α i₁ ⊑' α k)) → f (i₀ , d₀) ≡ f (i₁ , d₁)
    g (k , l , m) = 
     f (i₀ , d₀)                             ≡⟨ refl ⟩
     value (α i₀) d₀                         ≡⟨ ≡-of-values-from-≡ (l d₀) ⟩
     value (α k) (≡-to-is-defined (l d₀) d₀) ≡⟨ ≡-of-values-from-≡ ((m d₁) ⁻¹) ⟩
     value (α i₁) d₁                         ≡⟨ refl ⟩
     f (i₁ , d₁)                             ∎ 

 lifting-sup-value : {I : 𝓤₀ ̇}
                   → (α : I → 𝓛 X)
                   → (δ : is-directed _⊑'_ α )
                   → ∃ (\(i : I) → is-defined (α i)) → X
 lifting-sup-value {I} α δ = 
  constant-map-to-set-truncation-of-domain-map
   (Σ \(i : I) → is-defined (α i))
   s (family-value-map α) (directed-family-value-map-is-constant α δ)

 lifting-sup : {I : 𝓤₀ ̇} → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α) → 𝓛 X
 lifting-sup {I} α δ =
  ∃ (\(i : I) → is-defined (α i)) , lifting-sup-value α δ , ∥∥-is-a-prop

 lifting-sup-is-upperbound : {I : 𝓤₀ ̇} → (α : I → 𝓛 X) → (δ : is-directed _⊑'_ α)
                           → (i : I) → α i ⊑' lifting-sup α δ
 lifting-sup-is-upperbound {I} α δ i = γ where
  γ : α i ⊑' lifting-sup α δ
  γ = ⊑-to-⊑' (f , v) where
   f : is-defined (α i) → is-defined (lifting-sup α δ)
   f d = ∣ i , d ∣
   v : (d : is-defined (α i)) → value (α i) d ≡ value (lifting-sup α δ) (f d)
   v d = value (α i) d                 ≡⟨ constant-map-to-set-factors-through-truncation-of-domain
                                          (Σ (\(j : I) → is-defined (α j))) s
                                          (family-value-map α)
                                          (directed-family-value-map-is-constant α δ)
                                          (i , d) ⟩
         lifting-sup-value α δ (f d)   ≡⟨ refl ⟩
         value (lifting-sup α δ) (f d) ∎

 family-defined-somewhere-sup-≡ : {I : 𝓤₀ ̇} {α : I → 𝓛 X}
                                → (δ : is-directed _⊑'_ α)
                                → (i : I)
                                → is-defined (α i)
                                → α i ≡ lifting-sup α δ
 family-defined-somewhere-sup-≡ {I} {α} δ i d =
  (lifting-sup-is-upperbound α δ i) d

 lifting-sup-is-lowerbound-of-upperbounds : {I : 𝓤₀ ̇}
                                          → {α : I → 𝓛 X}
                                          → (δ : is-directed _⊑'_ α)
                                          → (v : 𝓛 X)
                                          → ((i : I) → α i ⊑' v)
                                          → lifting-sup α δ ⊑' v
 lifting-sup-is-lowerbound-of-upperbounds {I} {α} δ v b = h where
  h : lifting-sup α δ ⊑' v
  h d = ∥∥-rec (lifting-of-set-is-a-set fe fe pe X s) g d where
   g : (Σ (\(i : I) → is-defined (α i))) → lifting-sup α δ ≡ v
   g (i , dᵢ) = lifting-sup α δ ≡⟨ (family-defined-somewhere-sup-≡ δ i dᵢ) ⁻¹ ⟩
                α i             ≡⟨ b i dᵢ ⟩
                v               ∎

 𝓛-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO = 𝓛 X , _⊑'_ , sl , p , r , t , a , c where
  sl : is-set (𝓛 X)
  sl = lifting-of-set-is-a-set fe fe pe X s
  p : is-prop-valued (_⊑'_)
  p = ⊑'-prop-valued 
  r : is-reflexive (_⊑'_)
  r = ⊑'-is-reflexive
  a : is-antisymmetric (_⊑'_)
  a = ⊑'-is-antisymmetric
  t : is-transitive (_⊑'_)
  t = ⊑'-is-transitive
  c : (I : 𝓤₀ ̇) (α : I → 𝓛 X) → is-directed _⊑'_ α → has-sup _⊑'_ α
  c I α δ = lifting-sup α δ ,
            lifting-sup-is-upperbound α δ ,
            lifting-sup-is-lowerbound-of-upperbounds δ

 𝓛-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛-DCPO⊥ = 𝓛-DCPO , ⊥ , λ l → 𝟘-elim

module _
  {𝓤 : Universe}
  {𝓥 : Universe}
  {X : 𝓤 ̇}
  {Y : 𝓥 ̇}
  (s₀ : is-set X)
  (s₁ : is-set Y)
  where

 ♯-is-defined : (f : X → 𝓛 Y) (l : 𝓛 X) → is-defined ((f ♯) l) → is-defined l
 ♯-is-defined f l = pr₁

 ♯-on-total-element : (f : X → 𝓛 Y) {l : 𝓛 X} (d : is-defined l) → (f ♯) l ≡ f (value l d)
 ♯-on-total-element f {l} d = (f ♯) l               ≡⟨ ap (f ♯) (is-defined-η-≡ X s₀ d) ⟩
                              (f ♯) (η (value l d)) ≡⟨ ⋍-to-≡ Y s₁ (Kleisli-Law₁ f (value l d)) ⟩
                              f (value l d)         ∎
 
 ♯-is-monotone : (f : X → 𝓛 Y) → is-monotone (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (f ♯)
 ♯-is-monotone f l m ineq d = ap (f ♯) (ineq (♯-is-defined f l d))

 ♯-is-continuous : (f : X → 𝓛 Y) → is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (f ♯)
 ♯-is-continuous f I α δ = u , v where
  u : (i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ (f ♯) (∐ (𝓛-DCPO X s₀) δ)
  u i = ♯-is-monotone f (α i) (∐ (𝓛-DCPO X s₀) δ) (∐-is-upperbound (𝓛-DCPO X s₀) δ i)
  v : (m : ⟨ 𝓛-DCPO Y s₁ ⟩)
    → ((i : I) → (f ♯) (α i) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ m)
    → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ⊑⟨ (𝓛-DCPO Y s₁) ⟩ m
  v m ineqs d =
   ∥∥-rec (lifting-of-set-is-a-set fe fe pe Y s₁) g (♯-is-defined f (∐ (𝓛-DCPO X s₀) δ) d) where
    g : Σ (\(i : I) → is-defined (α i)) → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡ m
    g (i , dᵢ) = (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡⟨ h i dᵢ ⟩
                 (f ♯) (α i)               ≡⟨ ineqs i (≡-to-is-defined Y s₁ (h i dᵢ) d) ⟩
                 m                         ∎ where
     h : (i : I) → is-defined (α i) → (f ♯) (∐ (𝓛-DCPO X s₀) δ) ≡ (f ♯) (α i)
     h i d = ap (f ♯) ((family-defined-somewhere-sup-≡ X s₀ δ i d) ⁻¹)

 open import LiftingUnivalentPrecategory 𝓣 Y

 𝓛̇-♯-∼ : (f : X → Y) → (η ∘ f) ♯ ∼ 𝓛̇ f
 𝓛̇-♯-∼ f l = ⊑-anti pe fe fe (a , b) where
  a : ((η ∘ f) ♯) l ⊑ (𝓛̇ f) l
  a = p , q where
   p : is-defined (((η ∘ f) ♯) l) → is-defined (𝓛̇ f l)
   p = ♯-is-defined (η ∘ f) l
   q : (d : is-defined (((η ∘ f) ♯) l))
     → value (((η ∘ f) ♯) l) d ≡ value (𝓛̇ f l) (pr₁ d)
   q d = refl
  b : (𝓛̇ f) l ⊑ ((η ∘ f) ♯) l
  b = r , s where
   r : is-defined (𝓛̇ f l) → is-defined (((η ∘ f) ♯) l)
   r d = d , *
   s : (d : is-defined (𝓛̇ f l))
     → value (𝓛̇ f l) d ≡ value (((η ∘ f) ♯) l) (r d)
   s d = refl

 𝓛̇-continuous : (f : X → Y) → is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁) (𝓛̇ f)
 𝓛̇-continuous f = transport
                     (is-continuous (𝓛-DCPO X s₀) (𝓛-DCPO Y s₁))
                     (dfunext fe (𝓛̇-♯-∼ f))
                     (♯-is-continuous (η ∘ f)) where

𝓛ᵈℕ : DCPO⊥
𝓛ᵈℕ = 𝓛-DCPO⊥ ℕ ℕ-is-set

⦅ifZero⦆₀ : 𝓛 ℕ → 𝓛 ℕ → ℕ → 𝓛 ℕ
⦅ifZero⦆₀ a b zero     = a
⦅ifZero⦆₀ a b (succ n) = b

⦅ifZero⦆₁ : 𝓛 ℕ → 𝓛 ℕ → [ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] 
⦅ifZero⦆₁ a b = ((⦅ifZero⦆₀ a b) ♯) , ♯-is-continuous ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a b)

-- Find a better home for this
ℕ-cases : {P : ℕ → 𝓦 ̇} (n : ℕ) → (n ≡ zero → P n) → ((m : ℕ) → n ≡ succ m → P n) → P n
ℕ-cases {𝓦} {P} zero c₀ cₛ     = c₀ refl
ℕ-cases {𝓦} {P} (succ n) c₀ cₛ = cₛ n refl
--

⦅ifZero⦆₂ : 𝓛 ℕ → [ ⟪ 𝓛ᵈℕ ⟫ , DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] ]
⦅ifZero⦆₂ a = ⦅ifZero⦆₁ a , c
 where
  c : is-continuous ⟪ 𝓛ᵈℕ ⟫ DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] (⦅ifZero⦆₁ a)
  c I α δ = u , v
   where
    u : (i : I) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (α i)) ♯) l))
      → ((⦅ifZero⦆₀ a (α i)) ♯) l ≡ ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l
    u i l d = ((⦅ifZero⦆₀ a (α i)) ♯) l              ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (α i)) e ⟩
              ⦅ifZero⦆₀ a (α i) (value l e)          ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ a (α i) n ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) n} (value l e) p₀ pₛ ⟩
              ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e) ⁻¹ ⟩
              ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l     ∎
     where
      e : is-defined l
      e = ♯-is-defined ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (α i)) l d
      p₀ : value l e ≡ zero → ⦅ifZero⦆₀ a (α i) (value l e) ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
      p₀ q = ⦅ifZero⦆₀ a (α i) (value l e)          ≡⟨ ap (⦅ifZero⦆₀ a (α i)) q ⟩
             ⦅ifZero⦆₀ a (α i) zero                 ≡⟨ refl ⟩
             a                                     ≡⟨ refl ⟩
             ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero        ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) (q ⁻¹) ⟩
             ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ∎
      pₛ : (n : ℕ) → value l e ≡ succ n → ⦅ifZero⦆₀ a (α i) (value l e) ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
      pₛ n q = ⦅ifZero⦆₀ a (α i) (value l e)          ≡⟨ ap (⦅ifZero⦆₀ a (α i)) q ⟩
               ⦅ifZero⦆₀ a (α i) (succ n)             ≡⟨ refl ⟩
               α i                                    ≡⟨ family-defined-somewhere-sup-≡ ℕ ℕ-is-set δ i e₁ ⟩
               ∐ ⟪ 𝓛ᵈℕ ⟫ δ                            ≡⟨ refl ⟩
               ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (succ n)     ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) (q ⁻¹) ⟩
               ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ∎
       where
        e₁ : is-defined (α i)
        e₁ = ≡-to-is-defined ℕ ℕ-is-set (ap (⦅ifZero⦆₀ a (α i)) q)
             (≡-to-is-defined ℕ ℕ-is-set (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (α i)) {l} e) d)
    v : (f : ⟨ DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] ⟩)
      → ((i : I) → underlying-order DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] (⦅ifZero⦆₁ a (α i)) f)
      → (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l)) → ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l ≡ pr₁ f l
    v f ineqs l d = ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l     ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e ⟩
                    ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) n ≡ pr₁ f l} (value l e) p₀ pₛ ⟩
                    pr₁ f l                               ∎
     where
      e : is-defined l
      e = ♯-is-defined ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) l d
      p₀ : value l e ≡ zero → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡ pr₁ f l
      p₀ q = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
             ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero        ≡⟨ refl ⟩
             a                                     ≡⟨ r ⟩
             pr₁ f l                               ∎
       where
        r : a ≡ pr₁ f l
        r = ∥∥-rec (lifting-of-set-is-a-set fe fe pe ℕ ℕ-is-set) h (is-Directed-inhabited ⟪ 𝓛ᵈℕ ⟫ α δ)
         where
          h : (i : I) → a ≡ pr₁ f l
          h i = a                         ≡⟨ g ⟩
                ((⦅ifZero⦆₀ a (α i)) ♯) l ≡⟨ ineqs i l e₀ ⟩
                pr₁ f l                   ∎
           where
            g = a                             ≡⟨ refl ⟩
                ⦅ifZero⦆₀ a (α i) zero        ≡⟨ ap (⦅ifZero⦆₀ a (α i)) (q ⁻¹) ⟩
                ⦅ifZero⦆₀ a (α i) (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (α i)) e) ⁻¹ ⟩
                ((⦅ifZero⦆₀ a (α i)) ♯) l     ∎
            e₀ : is-defined (((⦅ifZero⦆₀ a (α i)) ♯) l)
            e₀ = ≡-to-is-defined ℕ ℕ-is-set (g' ∙ g) d
             where
              g' = ((⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) ♯) l     ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e ⟩
                   ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
                   ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) zero        ≡⟨ refl ⟩
                   a                                     ∎
            
      pₛ : (m : ℕ) → value l e ≡ succ m → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡ pr₁ f l
      pₛ m q = ∥∥-rec (lifting-of-set-is-a-set fe fe pe ℕ ℕ-is-set) h eₛ
       where
        g : (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) ♯) l ≡ ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e)
        g = ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) {l} e
        g' = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ ap (⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ)) q ⟩
             ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (succ m)    ≡⟨ refl ⟩
            ∐ ⟪ 𝓛ᵈℕ ⟫ δ                           ∎
        eₛ : is-defined (∐ ⟪ 𝓛ᵈℕ ⟫ δ)
        eₛ = ≡-to-is-defined ℕ ℕ-is-set (g ∙ g') d
        h : Σ (\(i : I) → is-defined (α i))
          → ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡ pr₁ f l
        h (i , dᵢ) = ⦅ifZero⦆₀ a (∐ ⟪ 𝓛ᵈℕ ⟫ δ) (value l e) ≡⟨ g' ⟩
                     ∐ ⟪ 𝓛ᵈℕ ⟫ δ                           ≡⟨ (family-defined-somewhere-sup-≡ ℕ ℕ-is-set δ i dᵢ) ⁻¹ ⟩
                     α i                                   ≡⟨ h' ⟩
                     ((⦅ifZero⦆₀ a (α i)) ♯) l              ≡⟨ ineqs i l (≡-to-is-defined ℕ ℕ-is-set h' dᵢ) ⟩
                     pr₁ f l                               ∎
         where
          h' = α i                           ≡⟨ refl ⟩
               ⦅ifZero⦆₀ a (α i) (succ m)    ≡⟨ ap (⦅ifZero⦆₀ a (α i)) (q ⁻¹) ⟩
               ⦅ifZero⦆₀ a (α i) (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ a (α i)) {l} e) ⁻¹ ⟩
               ((⦅ifZero⦆₀ a (α i)) ♯) l     ∎         

⦅ifZero⦆ : [ ⟪ 𝓛ᵈℕ ⟫ , DCPO[ ⟪ 𝓛ᵈℕ ⟫ , DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] ] ]
⦅ifZero⦆ = ⦅ifZero⦆₂ , c
 where
  c : is-continuous ⟪ 𝓛ᵈℕ ⟫ DCPO[ ⟪ 𝓛ᵈℕ ⟫ , DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] ] ⦅ifZero⦆₂
  c I α δ = u , v
   where
    u : (i : I) (b : 𝓛 ℕ) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ (α i) b) ♯) l))
      → ((⦅ifZero⦆₀ (α i) b) ♯) l ≡ ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l
    u i b l d = ((⦅ifZero⦆₀ (α i) b) ♯) l              ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (α i) b) e ⟩
                ⦅ifZero⦆₀ (α i) b (value l e)          ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ (α i) b n ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b n} (value l e) p₀ pₛ ⟩
                ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e) ⁻¹ ⟩
                ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l     ∎
     where
      e : is-defined l
      e = ♯-is-defined ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (α i) b) l d
      p₀ : value l e ≡ zero → ⦅ifZero⦆₀ (α i) b (value l e) ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
      p₀ q = ⦅ifZero⦆₀ (α i) b (value l e)                  ≡⟨ ap (⦅ifZero⦆₀ (α i) b) q ⟩
             ⦅ifZero⦆₀ (α i) b zero                         ≡⟨ refl ⟩
             α i                                            ≡⟨ family-defined-somewhere-sup-≡ ℕ ℕ-is-set δ i e₁ ⟩
             ∐ ⟪ 𝓛ᵈℕ ⟫ δ                                    ≡⟨ refl ⟩
             ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b zero                 ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) (q ⁻¹) ⟩
             ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)          ∎
       where
        e₁ : is-defined (α i)
        e₁ = ≡-to-is-defined ℕ ℕ-is-set (ap (⦅ifZero⦆₀ (α i) b) q)
             (≡-to-is-defined ℕ ℕ-is-set (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (α i) b) {l} e) d)
      pₛ : (n : ℕ) → value l e ≡ succ n → ⦅ifZero⦆₀ (α i) b (value l e) ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
      pₛ n q = ⦅ifZero⦆₀ (α i) b (value l e)          ≡⟨ ap (⦅ifZero⦆₀ (α i) b) q ⟩
               ⦅ifZero⦆₀ (α i) b (succ n)             ≡⟨ refl ⟩
               b                                     ≡⟨ refl ⟩
               ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ n)    ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) (q ⁻¹) ⟩
               ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ∎

    v : (f : ⟨ DCPO[ ⟪ 𝓛ᵈℕ ⟫ , DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] ] ⟩)
      → ((i : I) (b : 𝓛 ℕ) → underlying-order DCPO[ ⟪ 𝓛ᵈℕ ⟫ , ⟪ 𝓛ᵈℕ ⟫ ] (⦅ifZero⦆₁ (α i) b) (pr₁ f b))
      → (b : 𝓛 ℕ) (l : 𝓛 ℕ) (d : is-defined (((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l)) → ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l ≡ pr₁ (pr₁ f b) l 
    v f ineqs b l d = ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l     ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e ⟩
                      ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ ℕ-cases {𝓣 ⁺} {λ (n : ℕ) →  ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b n ≡ pr₁ (pr₁ f b) l} (value l e) p₀ pₛ ⟩
                      pr₁ (pr₁ f b) l                       ∎
     where
      e : is-defined l
      e = ♯-is-defined ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) l d
      p₀ : value l e ≡ zero → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡ pr₁ (pr₁ f b) l
      p₀ q = ∥∥-rec (lifting-of-set-is-a-set fe fe pe ℕ ℕ-is-set) h e₀
       where
        g : (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b ♯) l ≡ ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e)
        g = ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e
        g' = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
             ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b zero        ≡⟨ refl ⟩
             ∐ ⟪ 𝓛ᵈℕ ⟫ δ                           ∎
        e₀ : is-defined (∐ ⟪ 𝓛ᵈℕ ⟫ δ)
        e₀ = ≡-to-is-defined ℕ ℕ-is-set (g ∙ g') d
        h : Σ (\(i : I) → is-defined (α i))
          → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡ pr₁ (pr₁ f b) l
        h (i , dᵢ) = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ g' ⟩
                     ∐ ⟪ 𝓛ᵈℕ ⟫ δ                           ≡⟨ (family-defined-somewhere-sup-≡ ℕ ℕ-is-set δ i dᵢ) ⁻¹ ⟩
                     α i                                   ≡⟨ h' ⟩
                     ((⦅ifZero⦆₀ (α i) b) ♯) l              ≡⟨ ineqs i b l (≡-to-is-defined ℕ ℕ-is-set h' dᵢ) ⟩
                     pr₁ (pr₁ f b) l                       ∎
         where
          h' = α i                           ≡⟨ refl ⟩
               ⦅ifZero⦆₀ (α i) b zero        ≡⟨ ap (⦅ifZero⦆₀ (α i) b) (q ⁻¹) ⟩
               ⦅ifZero⦆₀ (α i) b (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (α i) b) {l} e) ⁻¹ ⟩
               ((⦅ifZero⦆₀ (α i) b) ♯) l     ∎         
            
      pₛ : (m : ℕ) → value l e ≡ succ m → ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡ pr₁ (pr₁ f b) l
      pₛ m q = ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
               ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ m)    ≡⟨ refl ⟩
               b                                     ≡⟨ r ⟩
               pr₁ (pr₁ f b) l                       ∎
       where
        r : b ≡ pr₁ (pr₁ f b) l
        r = ∥∥-rec (lifting-of-set-is-a-set fe fe pe ℕ ℕ-is-set) h (is-Directed-inhabited ⟪ 𝓛ᵈℕ ⟫ α δ)
         where
          h : (i : I) → b ≡ pr₁ (pr₁ f b) l
          h i = b                         ≡⟨ g ⟩
                ((⦅ifZero⦆₀ (α i) b) ♯) l ≡⟨ ineqs i b l eₛ ⟩
                pr₁ (pr₁ f b) l          ∎
           where
            g = b                             ≡⟨ refl ⟩
                ⦅ifZero⦆₀ (α i) b (succ m)    ≡⟨ ap (⦅ifZero⦆₀ (α i) b) (q ⁻¹) ⟩
                ⦅ifZero⦆₀ (α i) b (value l e) ≡⟨ (♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (α i) b) e) ⁻¹ ⟩
                ((⦅ifZero⦆₀ (α i) b) ♯) l     ∎
            eₛ : is-defined (((⦅ifZero⦆₀ (α i) b) ♯) l)
            eₛ = ≡-to-is-defined ℕ ℕ-is-set (g' ∙ g) d
             where
              g' = ((⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) ♯) l     ≡⟨ ♯-on-total-element ℕ-is-set ℕ-is-set (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) {l} e ⟩
                   ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (value l e) ≡⟨ ap (⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b) q ⟩
                   ⦅ifZero⦆₀ (∐ ⟪ 𝓛ᵈℕ ⟫ δ) b (succ m)    ≡⟨ refl ⟩
                   b                                     ∎

\end{code}
