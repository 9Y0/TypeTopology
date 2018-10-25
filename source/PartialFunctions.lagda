Martin Escardo 26th October 2018.

Only lifting for the moment. We will then discuss partial functions
(cf. my student Cory Knapp's PhD thesis).

We focuse, to begin with, on the fact that the canonical map into the
lifting is an embedding, which is easy for sets, but seems hard for
arbitrary types.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT

module PartialFunctions (V : Universe) where

open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Embedding
open import UF-FunExt
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Retracts

𝓛 : ∀ {U} → U ̇ → U ⊔ V ′ ̇
𝓛 {U} X = Σ \(P : V ̇) → is-prop P × (P → X)

η : ∀ {U} {X : U ̇} → X → 𝓛 X
η x = 𝟙 , 𝟙-is-prop , (λ _ → x)

\end{code}

Our strategy to show that η is an embedding is to show that it is the
composite of two embeddings (the first of which is actually an
equivalence).

\begin{code}

𝓜 : ∀ {U} → U ̇ → U ⊔ V ′ ̇
𝓜 {U} X = Σ \(P : V ̇) → is-singleton P × (P → X)

μ : ∀ {U} {X : U ̇} → X → 𝓜 X
μ x = 𝟙 , 𝟙-is-singleton , (λ _ → x)

ζ : ∀ {U} (X : U ̇) (P : V ̇) → is-singleton P × (P → X) → is-prop P × (P → X)
ζ X P (i , φ) = (is-singleton-is-prop i) , φ

eml : ∀ {U} (X : U ̇) → 𝓜 X → 𝓛 X
eml X = NatΣ (ζ X)

η-composite : funext V V → ∀ {U} → funext U (V ′ ⊔ U)
           → {X : U ̇} → η ≡ eml X ∘ μ
η-composite fe fe' = dfunext fe'
                         (λ x → to-Σ-≡ (refl ,
                                        (×-≡ (is-prop-is-prop fe _ _)
                                             refl)))

μ-is-equiv : propext V → funext V V → ∀ {U} → funext V U
          → {X : U ̇} → is-equiv (μ {U} {X})
μ-is-equiv pe fe {U} fe' {X} = qinv-is-equiv μ (ν , (νμ , μν))
 where
  ν : ∀ {U} {X : U ̇} → 𝓜 X → X
  ν (P , i , φ) = φ (is-singleton-pointed i)
  νμ : ∀ {U} {X : U ̇} → (x : X) → ν (μ x) ≡ x
  νμ x = refl
  μν : (m : 𝓜 X) → μ (ν m) ≡ m
  μν (P , i , φ) = to-Σ-≡ (t , s)
   where
    t : 𝟙 ≡ P
    t = pe 𝟙-is-prop (is-singleton-is-prop i) (λ _ → is-singleton-pointed i) (λ p → *)
    u :  transport (λ - → - → X) t (λ _ → φ (is-singleton-pointed i)) ≡ φ
    u = transport (λ - → - → X) t (λ _ → φ (is-singleton-pointed i))
            ≡⟨ transport-is-pre-comp t (λ _ → φ (is-singleton-pointed i)) ⟩
        (λ _ → φ (is-singleton-pointed i))
            ≡⟨ dfunext fe' (λ p → ap φ (is-singleton-is-prop i (is-singleton-pointed i) p)) ⟩
        φ   ∎
    s : transport (λ - → is-singleton - × (- → X)) t (𝟙-is-singleton , (λ _ → φ (is-singleton-pointed i)))
      ≡ i , φ
    s = transport (λ - → is-singleton - × (- → X)) t (𝟙-is-singleton , (λ _ → φ (is-singleton-pointed i)))
             ≡⟨ transport-× is-singleton (λ - → - → X) t ⟩
        transport is-singleton t 𝟙-is-singleton , transport (λ - → - → X) t (λ _ → φ (is-singleton-pointed i))
             ≡⟨ ×-≡ (is-prop-is-singleton fe _ i) u ⟩
        i , φ ∎

μ-is-embedding : propext V → funext V V → ∀ {U} → funext V U
               → {X : U ̇} → is-embedding (μ {U} {X})
μ-is-embedding pe fe fe' = is-equiv-is-embedding μ (μ-is-equiv pe fe fe')

eml-is-embedding : funext V V → ∀ {U} (X : U ̇)
                 → is-embedding (eml X)
eml-is-embedding fe {U} X =
  NatΣ-embedding
   (λ P → is-singleton P × (P → X))
   (λ P → is-prop P × (P → X))
   (ζ X)
   λ P → ×-embedding
             is-singleton-is-prop
             id
             (maps-of-props-are-embeddings
                is-singleton-is-prop
                (is-prop-is-singleton fe)
                (is-prop-is-prop fe))
             id-is-embedding

η-is-embedding : propext V → funext V V → ∀ {U} → funext V U → funext U (V ′ ⊔ U)
             → {X : U ̇} → is-embedding (η {U} {X})
η-is-embedding pe fe fe' fe'' {X} =
 back-transport
  is-embedding
  (η-composite fe fe'')
  (comp-embedding (μ-is-embedding pe fe fe') (eml-is-embedding fe X))

is-defined : ∀ {U} {X : U ̇} → 𝓛 X → V ̇
is-defined (P , i , φ) = P

is-defined-is-prop : ∀ {U} {X : U ̇} (l : 𝓛  X) → is-prop (is-defined l)
is-defined-is-prop (P , i , φ) = i

value : ∀ {U} {X : U ̇} (l : 𝓛  X) → is-defined l → X
value (P , i , φ) = φ

\end{code}

Information "Order" now:

\begin{code}

_⊑_ : ∀ {U} {X : U ̇} → 𝓛 X → 𝓛 X → U ⊔ V ̇
l ⊑ m = Σ \(f : is-defined l → is-defined m) → (d : is-defined l) → value l d ≡ value m (f d)

\end{code}

If X is a set, then 𝓛 X should be a poset under _⊑_. In the general
case, it should be some sort of univalent ∞-category.

\begin{code}

⊑-id : ∀ {U} {X : U ̇} (l : 𝓛 X) → l ⊑ l
⊑-id (P , i , φ) = id , (λ x → refl)

⊑-id' : ∀ {U} {X : U ̇} (l m : 𝓛 X) → l ≡ m → l ⊑ m
⊑-id' l m p = transport (λ - → l ⊑ -) p (⊑-id l)

⊑-∘ : ∀ {U} {X : U ̇} (l m n : 𝓛 X)
    → l ⊑ m → m ⊑ n → l ⊑ n
⊑-∘ l m n (f , δ) (g , ε) = g ∘ f , (λ d → δ d ∙ ε (f d))

⊑-anti : ∀ {U} → propext V → funext V V → funext V U
       → {X : U ̇} (l m : 𝓛 X) → (l ⊑ m) × (m ⊑ l) → l ≡ m
⊑-anti pe fe fe' {X} (Q , j , γ) (P , i , φ) ((f , δ) , (g , ε)) = e
 where
  a : Q ≡ P
  a = pe j i f g
  b : Idtofun (a ⁻¹) ≡ g
  b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))
  c : transport (λ - → is-prop - × (- → X)) a (j , γ)
    ≡ (transport is-prop a j , transport (λ - → - → X) a γ)
  c = transport-× is-prop (λ - → - → X) a
  d : pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ)) ≡ φ
  d = pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ))
            ≡⟨ ap pr₂ c ⟩
      transport (λ - → - → X) a γ
            ≡⟨ transport-is-pre-comp a γ ⟩
      γ ∘ Idtofun (a ⁻¹)
            ≡⟨ ap (λ - → γ ∘ -) b ⟩
      γ ∘ g
            ≡⟨ (dfunext fe' ε)⁻¹ ⟩
      φ     ∎
  e : Q , j , γ ≡ P , i , φ
  e = to-Σ-≡ (a , ×-≡ (is-prop-is-prop fe _ i) d)

\end{code}

We haven't used δ in the above proof. But we could use it instead of
ε, by definiting ε' from δ as follows, and then using (dfunext fe' ε')
instead of (dfunext fe' ε)⁻¹ in the above proof:

\begin{code}

  ε' : (p : P) → γ (g p) ≡ φ p
  ε' p = δ (g p) ∙ ap φ (i (f (g p)) p)

\end{code}

We now use this to show that for any l : 𝓛 X,

 fiber η l ≃ is-defined l

\begin{code}


η-fiber-same-as-is-defined :
    propext V → funext V V → ∀ {U} → funext V U → funext U (V ′ ⊔ U)
 → {X : U ̇} (l : 𝓛 X) → fiber η l ≃ is-defined l
η-fiber-same-as-is-defined pe fe {U} fe' fe'' {X} l =
 f l , ((g l , (λ d → is-defined-is-prop l (f l (g l d)) d)) ,
        (g l , λ z → η-is-embedding pe fe fe' fe'' l (g l (f l z)) z))
 where
  f : (l : 𝓛 X) → fiber η l → is-defined l
  f (.𝟙 , .𝟙-is-prop , .(λ _ → x)) (x , refl) = *

  g : (l : 𝓛 X) → is-defined l → fiber η l
  g (P , i , φ) p = φ p , a
   where
    a : η (φ p) ≡ (P , i , φ)
    a = ⊑-anti pe fe fe' (η (φ p))
                         (P , i , φ)
                         (((λ _ → p) , (λ _ → refl)) ,
                          ((λ _ → *) , (λ q → ap φ (i q p))))

\end{code}

They can't be equal, in the absence of cumulativity, as the lhs lives
in a universe higher than the rhs, even if U and V are the same
universe or if U = V ′. (But what if V = U ′? We can't this here as V
is a fixed module parameter.)

TODO: Could the map (anti l m) be an equivalence? No. We should
instead have an equivalence (l ⊑ m) × (m ⊑ l) → (l ≡ m) × (l ≡ m),
reflecting the fact that there were two candidate proofs for the
equality, as discussed above.

But I think it is better to have the following, which should be an
equivalence for each l and m:

\begin{code}

⊑-anti' : ∀ {U} → propext V → funext V V → funext V U

       → {X : U ̇} (l m : 𝓛 X) → (l ⊑ m) × (is-defined m → is-defined l) → l ≡ m
⊑-anti' pe fe fe' {X} (Q , j , γ) (P , i , φ) ((f , δ) , g) = e
 where
  ε' : (p : P) → γ (g p) ≡ φ p
  ε' p = δ (g p) ∙ ap φ (i (f (g p)) p)
  a : Q ≡ P
  a = pe j i f g
  b : Idtofun (a ⁻¹) ≡ g
  b = dfunext fe (λ p → j (Idtofun (a ⁻¹) p) (g p))
  c : transport (λ - → is-prop - × (- → X)) a (j , γ)
    ≡ (transport is-prop a j , transport (λ - → - → X) a γ)
  c = transport-× is-prop (λ - → - → X) a
  d : pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ)) ≡ φ
  d = pr₂ (transport (λ - → is-prop - × (- → X)) a (j , γ))
            ≡⟨ ap pr₂ c ⟩
      transport (λ - → - → X) a γ
            ≡⟨ transport-is-pre-comp a γ ⟩
      γ ∘ Idtofun (a ⁻¹)
            ≡⟨ ap (λ - → γ ∘ -) b ⟩
      γ ∘ g
            ≡⟨ dfunext fe' ε' ⟩
      φ     ∎
  e : Q , j , γ ≡ P , i , φ
  e = to-Σ-≡ (a , ×-≡ (is-prop-is-prop fe _ i) d)

⊑-anti'-inverse : ∀ {U}

       → {X : U ̇} (l m : 𝓛 X)  → l ≡ m → (l ⊑ m) × (is-defined m → is-defined l)
⊑-anti'-inverse l .l refl = (⊑-id l) , id

η-maximal : ∀ {U} {X : U ̇} (x : X) (l : 𝓛 X) → η x ⊑ l → l ⊑ η x
η-maximal x (P , i , γ) (f , δ) = (λ p → *) , (λ p → ap γ (i p (f *)) ∙ (δ *)⁻¹)

⊥ : ∀ {U} {X : U ̇} → 𝓛 X
⊥ = 𝟘 , 𝟘-is-prop , unique-from-𝟘

⊥-least : ∀ {U} {X : U ̇} (x : X) → ⊥ ⊑ η x
⊥-least x = unique-from-𝟘 , λ z → unique-from-𝟘 z


η-≡-gives-⊑ : ∀ {U} {X : U ̇} {x y : X} → x ≡ y → η x ⊑ η y
η-≡-gives-⊑ {U} {X} {x} {y} p = id , (λ d → p)

η-⊑-gives-≡ : ∀ {U} {X : U ̇} {x y : X} → η x ⊑ η y → x ≡ y
η-⊑-gives-≡ (f , δ) = δ *

η-≡-gives-⊑-is-equiv : ∀ {U} → funext V V → funext V U
                     → {X : U ̇} {x y : X} → is-equiv (η-≡-gives-⊑ {U} {X} {x} {y})
η-≡-gives-⊑-is-equiv {U} fe fe' {X} {x} {y} = qinv-is-equiv η-≡-gives-⊑ (η-⊑-gives-≡ , α , β)
 where
  α : {x y : X} (p : x ≡ y) →  η-⊑-gives-≡ (η-≡-gives-⊑ p) ≡ p
  α p = refl

  β : {x y : X} (a : η x ⊑ η y) → η-≡-gives-⊑ (η-⊑-gives-≡ a) ≡ a
  β (f , δ) = ×-≡ (dfunext fe (λ x → 𝟙-is-prop x (f x)))
                  (dfunext fe' (λ x → ap δ (𝟙-is-prop * x)))


{- TODO
⊑-directed-complete : ∀ {U} {X I : U ̇} (l : I → 𝓛 X)
                    → ((i j : I) → Σ \(k : I) → (l i ⊑ l k) × (l j ⊑ l k))
                    → Σ \(m : 𝓛 X) → ((i : I) → l i ⊑ m)
                                   × ((n : 𝓛 X) → ((i : I) → l i ⊑ n) → m ⊑ n)
⊑-directed-complete = {!!}
-}

\end{code}
