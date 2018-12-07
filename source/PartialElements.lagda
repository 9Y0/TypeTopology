Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting).
(Cf. my former student Cory Knapp's PhD thesis).

We focus, to begin with, on the fact that the canonical map into the
lifting is an embedding, which is easy for sets, but seems less easy for
arbitrary types.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT

module PartialElements where

open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Embedding
open import UF-FunExt
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Retracts

\end{code}

The domain of definition of a partial element is taken to be in an
arbitrary universe 𝓣.

\begin{code}

module _ (𝓣 : Universe) where

\end{code}

We discuss the type 𝓛 X of partial elements of a type X, also called
the lifting of X.

\begin{code}

 𝓛 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
 𝓛 X = Σ \(P : 𝓣 ̇) → is-prop P × (P → X)

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

 η : {X : 𝓤 ̇} → X → 𝓛 X
 η x = 𝟙 , 𝟙-is-prop , (λ _ → x)

\end{code}

Its "undefined" element:

\begin{code}

 ⊥ : {X : 𝓤 ̇} → 𝓛 X
 ⊥ = 𝟘 , 𝟘-is-prop , unique-from-𝟘

\end{code}

Our strategy to show that η is an embedding (has prop fibers)
is to exhibit it as the composite of two embeddings (the first of
which is actually an equivalence).

\begin{code}

 𝓚 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
 𝓚 X = Σ \(P : 𝓣 ̇) → is-singleton P × (P → X)

 κ : {X : 𝓤 ̇} → X → 𝓚 X
 κ x = 𝟙 , 𝟙-is-singleton , (λ _ → x)

 ζ : (X : 𝓤 ̇) (P : 𝓣 ̇) → is-singleton P × (P → X) → is-prop P × (P → X)
 ζ X P (i , φ) = singletons-are-props i , φ

 𝓚→𝓛 : (X : 𝓤 ̇) → 𝓚 X → 𝓛 X
 𝓚→𝓛 X = NatΣ (ζ X)

 η-composite : funext 𝓣 𝓣 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
             → {X : 𝓤 ̇} → η ≡ 𝓚→𝓛 X ∘ κ
 η-composite fe fe' {X} = dfunext fe' h
  where
   h : (x : X) → (𝟙 , 𝟙-is-prop ,                             λ _ → x)
               ≡ (𝟙 , singletons-are-props (𝟙-is-singleton) , λ _ → x)
   h x = to-Σ-≡ (refl , to-×-≡ (being-a-prop-is-a-prop fe _ _) refl)

\end{code}

The fact that 𝓚→𝓛 is an embedding can be proved by obtaining it as
a combination of maps that we already know to be embeddings, using
×-embedding, maps-of-props-are-embeddings, id-is-embedding, and
NatΣ-embedding.:

\begin{code}

 ζ-is-embedding : funext 𝓣 𝓣 → (X : 𝓤 ̇) (P : 𝓣 ̇) → is-embedding (ζ X P)
 ζ-is-embedding fe X P = ×-embedding
                           singletons-are-props
                           id
                           (maps-of-props-are-embeddings
                              singletons-are-props
                              (being-a-singleton-is-a-prop fe)
                              (being-a-prop-is-a-prop fe))
                           id-is-embedding

 𝓚→𝓛-is-embedding : funext 𝓣 𝓣
                       → (X : 𝓤 ̇) → is-embedding (𝓚→𝓛 X)
 𝓚→𝓛-is-embedding fe X = NatΣ-is-embedding
                                  (λ P → is-singleton P × (P → X))
                                  (λ P → is-prop P × (P → X))
                                  (ζ X)
                                  (ζ-is-embedding fe X)
\end{code}

That κ is an equivalence corresponds to the fact that the lifting of a
type X with respect to the dominance "is-singleton" is equivalent to X
itself.

\begin{code}

 κ-is-equiv : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
            → {X : 𝓤 ̇} → is-equiv (κ {𝓤} {X})
 κ-is-equiv {𝓤} pe fe fe' {X} = qinvs-are-equivs κ (ν , (νκ , κν))
  where
   ν : {X : 𝓤 ̇} → 𝓚 X → X
   ν (P , i , φ) = φ (singleton-types-are-pointed i)
   νκ : {X : 𝓤 ̇} (x : X) → ν (κ x) ≡ x
   νκ x = refl
   κν : (m : 𝓚 X) → κ (ν m) ≡ m
   κν (P , i , φ) = u
    where
     t : 𝟙 ≡ P
     t = pe 𝟙-is-prop (singletons-are-props i) (λ _ → singleton-types-are-pointed i) unique-to-𝟙
     s : (t : 𝟙 ≡ P)
       → transport (λ - → is-singleton - × (- → X)) t (𝟙-is-singleton , (λ _ → φ (singleton-types-are-pointed i)))
       ≡ i , φ
     s refl = to-×-≡ a b
       where
        a : 𝟙-is-singleton ≡ i
        a = (singletons-are-props (pointed-props-are-singletons 𝟙-is-singleton (being-a-singleton-is-a-prop fe))
                                  𝟙-is-singleton i)
        b : (λ x → φ (singleton-types-are-pointed i)) ≡ φ
        b = dfunext fe' (λ x → ap φ (𝟙-is-prop (singleton-types-are-pointed i) x))
     u : 𝟙 , 𝟙-is-singleton , (λ _ → φ (singleton-types-are-pointed i)) ≡ P , i , φ
     u = to-Σ-≡ (t , s t)

 κ-is-embedding : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
                → {X : 𝓤 ̇} → is-embedding (κ {𝓤} {X})
 κ-is-embedding pe fe fe' = equivs-are-embeddings κ (κ-is-equiv pe fe fe')

\end{code}

Finally, η is an embedding because it is equal to the composition of
two embeddings:

\begin{code}

 η-is-embedding : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
                → {X : 𝓤 ̇} → is-embedding (η {𝓤} {X})
 η-is-embedding pe fe fe' fe'' {X} =
   back-transport
    is-embedding
    (η-composite fe fe'')
    (comp-embedding (κ-is-embedding pe fe fe') (𝓚→𝓛-is-embedding fe X))
\end{code}

We now give meaningful names to the projections:

\begin{code}

 is-defined : {X : 𝓤 ̇} → 𝓛 X → 𝓣 ̇
 is-defined (P , i , φ) = P

 being-defined-is-a-prop : {X : 𝓤 ̇} (l : 𝓛  X) → is-prop (is-defined l)
 being-defined-is-a-prop (P , i , φ) = i

 value : {X : 𝓤 ̇} (l : 𝓛  X) → is-defined l → X
 value (P , i , φ) = φ

\end{code}

Next we show that for any l : 𝓛 X,

 fiber η l ≃ is-defined l,

using the fact that the fiber is a proposition by virtue of η being an
embedding.

For this purpose, it is convenient to work with the information
"order" on 𝓛 X, which will really be a (partial) order only when X is
a set:

\begin{code}

 _⊑_ : {X : 𝓤 ̇} → 𝓛 X → 𝓛 X → 𝓤 ⊔ 𝓣 ̇
 l ⊑ m = Σ \(f : is-defined l → is-defined m) → (d : is-defined l) → value l d ≡ value m (f d)

\end{code}

If X is a set, then 𝓛 X is a poset under _⊑_ (TODO). In the general
case, it should be some sort of univalent ∞-category with
hom-∞-groupoids x ⊑ y.

\begin{code}

 ⊑-id : {X : 𝓤 ̇} (l : 𝓛 X) → l ⊑ l
 ⊑-id (P , i , φ) = id , (λ x → refl)

 ⊑-id' : {X : 𝓤 ̇} (l m : 𝓛 X) → l ≡ m → l ⊑ m
 ⊑-id' l m p = transport (λ - → l ⊑ -) p (⊑-id l)

 ⊑-∘ : {X : 𝓤 ̇} (l m n : 𝓛 X)
     → l ⊑ m → m ⊑ n → l ⊑ n
 ⊑-∘ l m n (f , δ) (g , ε) = g ∘ f , (λ d → δ d ∙ ε (f d))

 ⊑-anti : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
        → {X : 𝓤 ̇} {l m : 𝓛 X}
        → (l ⊑ m) × (m ⊑ l) → l ≡ m
 ⊑-anti pe fe fe' {X} {Q , j , γ} {P , i , φ} ((f , δ) , (g , ε)) = e
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
   e = to-Σ-≡ (a , to-×-≡ (being-a-prop-is-a-prop fe _ i) d)

\end{code}

We haven't used δ in the above proof. But we could use it instead of
ε, by defining ε' from δ as follows, and then using (dfunext fe' ε')
instead of (dfunext fe' ε)⁻¹ in the above proof:

\begin{code}

   ε' : (p : P) → γ (g p) ≡ φ p
   ε' p = δ (g p) ∙ ap φ (i (f (g p)) p)

\end{code}

We can now establish the promised fact:

\begin{code}

 η-fiber-same-as-is-defined :
     propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
   → {X : 𝓤 ̇} (l : 𝓛 X)
   → (Σ \(x : X) → η x ≡ l) ≃ is-defined l
 η-fiber-same-as-is-defined pe fe fe' fe'' {X} l = f l , ((g l , fg) , (g l , gf))
  where
   f : (l : 𝓛 X) → fiber η l → is-defined l
   f (.𝟙 , .𝟙-is-prop , .(λ _ → x)) (x , refl) = *
   g : (l : 𝓛 X) → is-defined l → fiber η l
   g (P , i , φ) p = φ p , ⊑-anti pe fe fe' (a , b)
    where
     a : η (φ p) ⊑ (P , i , φ)
     a = (λ _ → p) , (λ _ → refl)
     b : (P , i , φ) ⊑ η (φ p)
     b = (λ _ → *) , (λ q → ap φ (i q p))
   fg : (d : is-defined l) → f l (g l d) ≡ d
   fg d = being-defined-is-a-prop l (f l (g l d)) d
   gf : (z : fiber η l) → g l (f l z) ≡ z
   gf z = η-is-embedding pe fe fe' fe'' l (g l (f l z)) z

\end{code}

They can't be equal, in the absence of cumulativity (and propositional
resizing), as the lhs lives in a universe higher than the rhs, and
equality is well-typed only for elements of the same type (here of the
same universe). This can be seen by adding type annotations to the
formulation of the above equivalence:

\begin{code}

 private
  η-fiber-same-as-is-defined' :
       propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤 → funext 𝓤 (𝓣 ⁺ ⊔ 𝓤)
    → {X : 𝓤 ̇} (l : 𝓛 X)
    → (fiber η l ∶ 𝓣 ⁺ ⊔ 𝓤 ̇) ≃ (is-defined l ∶ 𝓣 ̇)
  η-fiber-same-as-is-defined' = η-fiber-same-as-is-defined

\end{code}

For no choice of universes 𝓤 and 𝓣 can we have 𝓣 ' ⊔ 𝓤 to coincide
with 𝓣. However, for some dominances other than is-prop, it is possible to
have the equality between the fiber of l and the definedness of l.

TODO: Could the map (anti l m) be an equivalence? No. We should
instead have an equivalence (l ⊑ m) × (m ⊑ l) → (l ≡ m) × (l ≡ m),
reflecting the fact that there were two candidate proofs for the
equality, as discussed above.

But it is probably better to have the following version of ⊑-anti,
which should be an equivalence for each l and m:

\begin{code}

 ⊑-anti' : propext 𝓣 → funext 𝓣 𝓣 → funext 𝓣 𝓤
         → {X : 𝓤 ̇} (l m : 𝓛 X) → (l ⊑ m) × (is-defined m → is-defined l) → l ≡ m
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
   e = to-Σ-≡ (a , to-×-≡ (being-a-prop-is-a-prop fe _ i) d)


 ⊑-anti'-inverse :  {X : 𝓤 ̇} (l m : 𝓛 X)
                 → l ≡ m → (l ⊑ m) × (is-defined m → is-defined l)
 ⊑-anti'-inverse l .l refl = ⊑-id l , id

 η-maximal : {X : 𝓤 ̇} (x : X) (l : 𝓛 X) → η x ⊑ l → l ⊑ η x
 η-maximal x (P , i , γ) (f , δ) = (λ p → *) , (λ p → ap γ (i p (f *)) ∙ (δ *)⁻¹)

 ⊥-least : {X : 𝓤 ̇} (x : X) → ⊥ ⊑ η x
 ⊥-least x = unique-from-𝟘 , λ z → unique-from-𝟘 z


 η-≡-gives-⊑ : {X : 𝓤 ̇} {x y : X} → x ≡ y → η x ⊑ η y
 η-≡-gives-⊑ {𝓤} {X} {x} {y} p = id , (λ d → p)

 η-⊑-gives-≡ : {X : 𝓤 ̇} {x y : X} → η x ⊑ η y → x ≡ y
 η-⊑-gives-≡ (f , δ) = δ *

 η-≡-gives-⊑-is-equiv : funext 𝓣 𝓣 → funext 𝓣 𝓤
                      → {X : 𝓤 ̇} {x y : X}
                      → is-equiv (η-≡-gives-⊑ {𝓤} {X} {x} {y})
 η-≡-gives-⊑-is-equiv {𝓤} fe fe' {X} {x} {y} = qinvs-are-equivs η-≡-gives-⊑ (η-⊑-gives-≡ , α , β)
  where
   α : {x y : X} (p : x ≡ y) →  η-⊑-gives-≡ (η-≡-gives-⊑ p) ≡ p
   α p = refl

   β : {x y : X} (q : η x ⊑ η y) → η-≡-gives-⊑ (η-⊑-gives-≡ q) ≡ q
   β (f , δ) = to-×-≡ (dfunext fe (λ x → 𝟙-is-prop x (f x)))
                      (dfunext fe' (λ x → ap δ (𝟙-is-prop * x)))


{- TODO
⊑-directed-complete : {X I : 𝓤 ̇} (l : I → 𝓛 X)
                    → ((i j : I) → Σ \(k : I) → (l i ⊑ l k) × (l j ⊑ l k))
                    → Σ \(m : 𝓛 X) → ((i : I) → l i ⊑ m)
                                   × ((n : 𝓛 X) → ((i : I) → l i ⊑ n) → m ⊑ n)
⊑-directed-complete = {!!}
-}

\end{code}

We should also do least fixed points of continuous maps.

Added 7th November 2018. 'Monad' structure on 𝓛.

\begin{code}

 _♯ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → 𝓛 Y) → (𝓛 X → 𝓛 Y)
 _♯ f (P , i , φ) = (Σ \(p : P) → is-defined (f (φ p))) ,
                     Σ-is-prop i (λ p → being-defined-is-a-prop (f (φ p))) ,
                     λ σ → value (f (φ (pr₁ σ))) (pr₂ σ)

{-
 kleisli-law₀ : {X : 𝓤 ̇} → (η {𝓤} {X})♯ ∼ id
 kleisli-law₀ {𝓤} {X} (P , i , φ) = {!!}

 kleisli-law₁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → 𝓛 Y) → f ♯ ∘ η ∼ f
 kleisli-law₁ f x = {!!}

 kleisli-law₂ : {X : 𝓥 ̇} {Y : 𝓦 ̇} {Z : 𝓣 ̇} (f : X → 𝓛 Y) (g : Y → 𝓛 Z)
              → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
 kleisli-law₂ = {!!}
-}

 𝓛→ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
 𝓛→ f (P , i , φ) = P , i , f ∘ φ

 𝓛→' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓛 X → 𝓛 Y
 𝓛→' f = (η ∘ f)♯
{-
 𝓛→-agreement : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → 𝓛→ f ∼ 𝓛→' f
 𝓛→-agreement {𝓤} {𝓥} {X} {Y} f (P , i , φ) = {!!}
-}

 𝓛-id : {X : 𝓤 ̇} → 𝓛→ id ≡ id
 𝓛-id {𝓤} {X} = refl {𝓤 ⊔ (𝓣 ⁺)} {𝓛 X → 𝓛 X}

 𝓛-∘ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} (f : X → Y) (g : Y → Z)
     → 𝓛→ (g ∘ f) ≡ 𝓛→ g ∘ 𝓛→ f
 𝓛-∘ f g = refl

 η-natural : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → η ∘ f ≡ 𝓛→ f ∘ η
 η-natural f = refl

 μ : {X : 𝓤 ̇} → 𝓛 (𝓛 X) → 𝓛 X
 μ = id ♯

{-
 μ-natural : {X : 𝓤 ̇} {Y : 𝓤 ̇} (f : X → Y) → 𝓛→ f ∘ μ ≡ μ ∘ 𝓛→ (𝓛→ f)
 μ-natural f = {!!}

 𝓛-unit₀ : {X : 𝓤 ̇} → μ ∘ 𝓛→ (η {_} {X}) ≡ id
 𝓛-unit₀ = {!!}

 𝓛-unit₁ : {X : 𝓤 ̇} → μ ∘ (η {_} {𝓛 X}) ≡ id
 𝓛-unit₁ = {!!}

 𝓛-assoc : {X : 𝓤 ̇} → μ ∘ (μ {_} {𝓛 X}) ≡ μ ∘ 𝓛→ (μ {_} {X})
 𝓛-assoc = {!!}
-}

\end{code}

Added 8th November 2018.

\begin{code}

 pus : {X : 𝓤 ̇} {P : 𝓣 ̇} → 𝓛 X → (P → 𝓛 X)
 pus l p = l

 sup : {X : 𝓤 ̇} {P : 𝓣 ̇} → is-prop P → (P → 𝓛 X) → 𝓛 X
 sup {𝓤} {X} {P} i φ = μ (P , i , φ)

{-
sup-adj : (𝓣 : Universe) {X : 𝓤 ̇} (P : 𝓣 ̇) (i : is-prop P) (φ : P → 𝓛 𝓣 X) (l : 𝓛 𝓣 X)
        → (_⊑_ 𝓣 (sup 𝓣 i φ) l) ≃ ((p : P) → _⊑_ 𝓣 (φ p) l)
sup-adj = {!!}

sup-reflective : (𝓣 : Universe) {X : 𝓤 ̇} (P : 𝓣 ̇) (i : is-prop P) (φ : P → 𝓛 𝓣 X) (l : 𝓛 𝓣 X)
               → (p : P) → φ p ≡ sup 𝓣 i φ
sup-reflective 𝓣 P i φ l p = {!!}
-}

\end{code}

This has a connection with injectivity.

Another way to define μ, which has different universe level:

\begin{code}

𝓛* : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) → is-embedding f → 𝓛 𝓣 Y → 𝓛 (𝓤 ⊔ 𝓥 ⊔ 𝓣) X
𝓛* f e (Q , j , γ) = (Σ \(q : Q) → fiber f (γ q)) ,
                      Σ-is-prop j (e ∘ γ) ,
                      λ p → pr₁ (pr₂ p)

μ* : (𝓣 𝓣' : Universe) {X : 𝓤 ̇} → funext 𝓣 𝓣 → funext 𝓣' 𝓣' → funext 𝓣' 𝓤 → funext 𝓤 (𝓤 ⊔ (𝓣' ⁺)) → propext 𝓣'
  → 𝓛 𝓣 (𝓛 𝓣' X) → 𝓛 (𝓤 ⊔ 𝓣 ⊔ (𝓣' ⁺)) X
μ* {𝓤} 𝓣 𝓣' {X} fe fe' fe'' fe''' pe = 𝓛* (η 𝓣') (η-is-embedding 𝓣' pe fe' fe'' fe''')

\end{code}
