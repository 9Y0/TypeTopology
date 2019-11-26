Martin Escardo, 2017, written in Agda November 2019.

We prove Coquand and Danielsson's result that if X is discrete then

  (X + 𝟙) × X ! ≃ (X + 𝟙)!

where

  ! X = (X ≃ X),

more commonly written Aut X.

We then generalize it to show that, without any assumptions on X,

  co-derived-set (X + 𝟙) × X ! ≃ (X + 𝟙)!

where the co-derived-set of a type is the subtype of isolated points.

For example, the circle S¹ doesn't have any isolated points, so that
the co-derived-set of S¹ + 𝟙 is equivalent to 𝟙, and hence

  S¹ ! ≃ (S¹ + 𝟙)!

More generally this is the case for any connected type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

\end{code}

We need functional extensionality (but not propositional
extensionality or univalence):

\begin{code}

module UF-Factorial (fe : FunExt) where

open import SpartanMLTT
open import Plus-Properties
open import DiscreteAndSeparated
open import UF-Base
open import UF-Retracts
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import UF-Miscelanea
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Subsingletons
open import UF-Equiv-FunExt
open import UF-Miscelanea

\end{code}

We refer to set of isolated points as the co derived set (for
complement of the derived set, in the sense of Cantor, consisting of
the limit points, i.e. non-isolated points).

Recall that a point x : X is isolated if the identity type x ≡ y is
decidable for every y : X.

\begin{code}

co-derived-set : 𝓤 ̇ → 𝓤 ̇
co-derived-set X = Σ \(x : X) → is-isolated x

cods-embedding : (X : 𝓤 ̇ ) → co-derived-set X → X
cods-embedding X = pr₁

cods-embedding-is-embedding : (X : 𝓤 ̇ ) → is-embedding (cods-embedding X)
cods-embedding-is-embedding X = pr₁-is-embedding (being-isolated-is-a-prop fe)

cods-embedding-is-equiv : (X : 𝓤 ̇ ) → is-discrete X → is-equiv (cods-embedding X)
cods-embedding-is-equiv X d = pr₁-is-equiv X is-isolated
                               (λ x → pointed-props-are-singletons (d x)
                                       (being-isolated-is-a-prop fe x))

≃-cods : (X : 𝓤 ̇ ) → is-discrete X → co-derived-set X ≃ X
≃-cods X d = cods-embedding X , cods-embedding-is-equiv X d

\end{code}

Recall that a type is perfect if it has no isolated points.

\begin{code}

perfect-coderived-empty : (X : 𝓤 ̇ ) → is-perfect X → is-empty (co-derived-set X)
perfect-coderived-empty X i = γ
 where
  γ : co-derived-set X → 𝟘
  γ (x , j) = i (x , j)

perfect-coderived-singleton : (X : 𝓤 ̇ ) → is-perfect X → is-singleton (co-derived-set (X + 𝟙 {𝓥}))
perfect-coderived-singleton X i = (inr * , new-point-is-isolated) , γ
 where
  γ : (c : co-derived-set (X + 𝟙)) → inr * , new-point-is-isolated ≡ c
  γ (inl x , j) = 𝟘-elim (i (x , a))
   where
    a : is-isolated x
    a = embeddings-reflect-isolatedness inl (inl-is-embedding X 𝟙) x j
  γ (inr * , j) = to-Σ-≡' (being-isolated-is-a-prop fe (inr *) new-point-is-isolated j)

\end{code}

We change the value of one isolated argument of a function, and no
other value, with patch:

\begin{code}

patch : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
      → is-isolated a → (X → Y) → (X → Y)
patch a b i f x = Cases (i x)
                    (λ (_ : a ≡ x) → b)
                    (λ (_ : a ≢ x) → f x)

patch-equation₀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → patch a b i f a ≡ b
patch-equation₀ a b i f = Cases-equality-l (λ _ → b) (λ _ → f a) (i a) refl γ
 where
  γ : i a ≡ inl refl
  γ = isolated-inl a i a refl

patch-equation₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → (x : X) → a ≢ x → patch a b i f x ≡ f x
patch-equation₁ {𝓤} {X} a b i f x n = Cases-equality-r (λ _ → b) (λ _ → f x) (i x) n γ
 where
  γ : i x ≡ inr n
  γ = isolated-inr (fe 𝓤 𝓤₀) a i x n

\end{code}

The (involutive) swap automorphism is obtained by patching the
identity function twice:

\begin{code}

swap : {X : 𝓤 ̇ } (a b : X) → is-isolated a → is-isolated b → X → X
swap a b i j = patch a b i (patch b a j id)

swap-equation₀ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j a ≡ b
swap-equation₀ a b i j = patch-equation₀ a b i (patch b a j id)

swap-equation₁ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j b ≡ a
swap-equation₁ a b i j = γ (j a)
 where
  γ : (b ≡ a) + (b ≢ a) → swap a b i j b ≡ a
  γ (inl r) =
      swap a b i j b ≡⟨ ap (swap a b i j) r    ⟩
      swap a b i j a ≡⟨ swap-equation₀ a b i j ⟩
      b              ≡⟨ r                      ⟩
      a              ∎
  γ (inr n) =
      swap a b i j b                 ≡⟨ refl                                               ⟩
      patch a b i (patch b a j id) b ≡⟨ patch-equation₁ a b i (patch b a j id) b (≢-sym n) ⟩
      patch b a j id b               ≡⟨ patch-equation₀ b a j id                           ⟩
      a                              ∎

swap-equation₂ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → (x : X) → a ≢ x → b ≢ x → swap a b i j x ≡ x
swap-equation₂ a b i j x m n =
  swap a b i j x                 ≡⟨ refl                                       ⟩
  patch a b i (patch b a j id) x ≡⟨ patch-equation₁ a b i (patch b a j id) x m ⟩
  patch b a j id x               ≡⟨ patch-equation₁ b a j id x n               ⟩
  x                              ∎

swap-symmetric : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j ∼ swap b a j i
swap-symmetric a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j x ≡ swap b a j i x
  γ (inl p) _ =
    swap a b i j x ≡⟨ ap (swap a b i j) (p ⁻¹)         ⟩
    swap a b i j a ≡⟨ swap-equation₀ a b i j           ⟩
    b              ≡⟨ (swap-equation₁ b a j i)⁻¹       ⟩
    swap b a j i a ≡⟨ ap (swap b a j i) p              ⟩
    swap b a j i x ∎
  γ (inr _) (inl q) =
    swap a b i j x ≡⟨ ap (swap a b i j) (q ⁻¹)         ⟩
    swap a b i j b ≡⟨ swap-equation₁ a b i j           ⟩
    a              ≡⟨ (swap-equation₀ b a j i)⁻¹       ⟩
    swap b a j i b ≡⟨ ap (swap b a j i) q              ⟩
    swap b a j i x ∎
  γ (inr m) (inr n) =
    swap a b i j x ≡⟨ swap-equation₂ a b i j x m n     ⟩
    x              ≡⟨ (swap-equation₂ b a j i x n m)⁻¹ ⟩
    swap b a j i x ∎

swap-involutive : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
                → swap a b i j ∘ swap a b i j ∼ id
swap-involutive a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j (swap a b i j x) ≡ x
  γ (inl p) _ =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (p ⁻¹)  ⟩
    swap a b i j (swap a b i j a) ≡⟨ ap (swap a b i j) (swap-equation₀ a b i j)       ⟩
    swap a b i j b                ≡⟨ swap-equation₁ a b i j                           ⟩
    a                             ≡⟨ p                                                ⟩
    x                             ∎
  γ (inr _) (inl q) =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (q ⁻¹)  ⟩
    swap a b i j (swap a b i j b) ≡⟨ ap (swap a b i j) (swap-equation₁ a b i j)       ⟩
    swap a b i j a                ≡⟨ swap-equation₀ a b i j                           ⟩
    b                             ≡⟨ q                                                ⟩
    x                             ∎
  γ (inr m) (inr n) =
    swap a b i j (swap a b i j x) ≡⟨ ap (swap a b i j) (swap-equation₂ a b i j x m n) ⟩
    swap a b i j x                ≡⟨ swap-equation₂ a b i j x m n                     ⟩
    x                             ∎

swap-is-equiv : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
              → is-equiv (swap a b i j)
swap-is-equiv a b i j = qinvs-are-equivs
                         (swap a b i j)
                         (swap a b i j , (swap-involutive a b i j , swap-involutive a b i j))

≃-swap : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b) → X ≃ X
≃-swap a b i j = swap a b i j , swap-is-equiv a b i j

\end{code}

For a type A, denote by A' the co-derived set of A.

Then we get a map

  (Y+1)' × (X ≃ Y) → (X+1 ≃ Y+1),

where the choice of isolated point a:Y+1 controls which equivalence
X+1≃Y+1 we get from the equivalence f: X≃Y:

       f+1       swap(a,inr(⋆))
  X+1 ----> Y+1 ---------------> Y+1

The claim is that the above map is an equivalence.

We construct/prove this in four steps:

(1)  (X ≃ Y)
    ≃ Σ \(f : X + 𝟙 ≃ Y + 𝟙) → f (inr *) ≡ inr *

Hence

(2) (Y + 𝟙)' × (X ≃ Y)
  ≃ (Y + 𝟙)' × Σ \(f : X + 𝟙 ≃ Y + 𝟙) → f (inr *) ≡ inr *

Also

(3) (Y + 𝟙)' × (Σ \(f : X + 𝟙 ≃ Y + 𝟙) → f (inr *) ≡ inr *)
  ≃ (X + 𝟙 ≃ Y + 𝟙)

And therefore

(4) (Y + 𝟙)' × (X ≃ Y)
  ≃ (X + 𝟙 ≃ Y + 𝟙)

\begin{code}

module factorial-steps
        {𝓤 𝓥 : Universe}
        (𝓦 𝓣 : Universe)
        (X : 𝓤 ̇ )
        (Y : 𝓥 ̇ )
       where

 X+𝟙 = X + 𝟙 {𝓦}
 Y+𝟙 = Y + 𝟙 {𝓣}

 lemma₀ : (f : X+𝟙 → Y+𝟙)
        → f (inr *) ≡ inr *
        → is-section f
        → (x : X) → Σ \(y : Y) → f (inl x) ≡ inl y
 lemma₀ f p (g , gf) x = γ x (f (inl x)) refl
  where
   γ : (x : X) (z : Y+𝟙) → f (inl x) ≡ z → Σ \(y : Y) → z ≡ inl y
   γ x (inl y) q = y , refl
   γ x (inr *) q = 𝟘-elim (+disjoint (inl x         ≡⟨ (gf (inl x))⁻¹ ⟩
                                      g (f (inl x)) ≡⟨ ap g q         ⟩
                                      g (inr *)     ≡⟨ ap g (p ⁻¹)    ⟩
                                      g (f (inr *)) ≡⟨ gf (inr *)     ⟩
                                      inr *         ∎))
\end{code}

The following is the same as the above with X and Y swapped. It seems
easier and shorter to repeat the proof than to make the above more
general and have X and Y as module parameters:

\begin{code}

 lemma₁ : (g : Y+𝟙 → X+𝟙)
        → g (inr *) ≡ inr *
        → is-section g
        → (y : Y) → Σ \(x : X) → g (inl y) ≡ inl x
 lemma₁ g p (f , fg) y = γ y (g (inl y)) refl
  where
   γ : (y : Y) (t : X+𝟙) → g (inl y) ≡ t → Σ \(x : X) → t ≡ inl x
   γ y (inl x) q = x , refl
   γ y (inr *) q = 𝟘-elim (+disjoint (inl y         ≡⟨ (fg (inl y))⁻¹ ⟩
                                      f (g (inl y)) ≡⟨ ap f q         ⟩
                                      f (inr *)     ≡⟨ ap f (p ⁻¹)    ⟩
                                      f (g (inr *)) ≡⟨ fg (inr *)     ⟩
                                      inr *         ∎))

 lemma₂ : (f : X+𝟙 → Y+𝟙)
        → f (inr *) ≡ inr *
        → is-equiv f
        → Σ \(f' : X → Y) → is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
 lemma₂ f p i = γ (equivs-are-qinvs f i)
  where
   γ : qinv f → Σ \(f' : X → Y) → is-equiv f' × (f ∼ +functor f' unique-to-𝟙)
   γ (g , η , ε) = f' , qinvs-are-equivs f' (g' , η' , ε') , h
    where
     f' : X → Y
     f' x = pr₁ (lemma₀ f p (g , η) x)

     a : (x : X) → f (inl x) ≡ inl (f' x)
     a x = pr₂ (lemma₀ f p (g , η) x)

     q = g (inr *)     ≡⟨ (ap g p)⁻¹ ⟩
         g (f (inr *)) ≡⟨ η (inr *)  ⟩
         inr *         ∎

     g' : Y → X
     g' x = pr₁ (lemma₁ g q (f , ε) x)

     b : (y : Y) → g (inl y) ≡ inl (g' y)
     b y = pr₂ (lemma₁ g q (f , ε) y)

     η' : g' ∘ f' ∼ id
     η' x = inl-lc (inl (g' (f' x)) ≡⟨ (b (f' x))⁻¹   ⟩
                    g (inl (f' x))  ≡⟨ (ap g (a x))⁻¹ ⟩
                    g (f (inl x))   ≡⟨ η (inl x)      ⟩
                    inl x           ∎)

     ε' : f' ∘ g' ∼ id
     ε' y = inl-lc (inl (f' (g' y)) ≡⟨ (a (g' y))⁻¹   ⟩
                    f (inl (g' y))  ≡⟨ (ap f (b y))⁻¹ ⟩
                    f (g (inl y))   ≡⟨ ε (inl y)      ⟩
                    inl y           ∎)

     h : f ∼ +functor f' unique-to-𝟙
     h (inl x) = a x
     h (inr *) = p


 step₁ : (X ≃ Y) ≃ Σ \(f : X+𝟙 ≃ Y+𝟙) → ⌜ f ⌝ (inr *) ≡ inr *
 step₁ = φ , (γ , η) , (γ , ε)
  where
   a : (g : X → Y) → qinv g → Y+𝟙 → X+𝟙
   a g (g' , η , ε) = +functor g' unique-to-𝟙

   b : (g : X → Y) (q : qinv g) → a g q ∘ +functor g unique-to-𝟙 ∼ id
   b g (g' , η , ε) (inl x) = ap inl (η x)
   b g (g' , η , ε) (inr *) = refl

   c : (g : X → Y) (q : qinv g) → +functor g unique-to-𝟙 ∘ a g q ∼ id
   c g (g' , η , ε) (inl y) = ap inl (ε y)
   c g (g' , η , ε) (inr *) = refl

   d : (g : X → Y) → qinv g → is-equiv (+functor g unique-to-𝟙)
   d g q = qinvs-are-equivs (+functor g unique-to-𝟙) (a g q , b g q , c g q)

   φ : (X ≃ Y) → Σ \(e : X+𝟙 ≃ Y+𝟙) → ⌜ e ⌝ (inr *) ≡ inr *
   φ (g , i) = (+functor g unique-to-𝟙 , d g (equivs-are-qinvs g i)) , refl

   γ : (Σ \(e : X+𝟙 ≃ Y+𝟙) → ⌜ e ⌝ (inr *) ≡ inr *) → (X ≃ Y)
   γ ((f , i) , p) = pr₁ (lemma₂ f p i) , pr₁ (pr₂ (lemma₂ f p i))

   η : φ ∘ γ ∼ id
   η ((f , i) , p) = to-Σ-≡
                      (to-subtype-≡ (being-equiv-is-a-prop fe) r ,
                      isolated-is-h-isolated (f (inr *))
                       (equivs-preserve-isolatedness f i (inr *) new-point-is-isolated) _ p)
    where
     s : f ∼ pr₁ (pr₁ ((φ ∘ γ) ((f , i) , p)))
     s (inl x) = pr₂ (pr₂ (lemma₂ f p i)) (inl x)
     s (inr *) = p

     r : pr₁ (pr₁ ((φ ∘ γ) ((f , i) , p))) ≡ f
     r = dfunext (fe _ _) (λ z → (s z)⁻¹)

   ε : γ ∘ φ ∼ id
   ε (g , i) = to-Σ-≡ (refl , being-equiv-is-a-prop fe g _ i)


 step₂ : co-derived-set (Y+𝟙) × (X ≃ Y)
       ≃ co-derived-set (Y+𝟙) × Σ \(e : X+𝟙 ≃ Y+𝟙) → ⌜ e ⌝ (inr *) ≡ inr *
 step₂ = ×cong (≃-refl (co-derived-set (Y+𝟙))) step₁


 step₃ : (co-derived-set (Y+𝟙) × Σ \(e : X+𝟙 ≃ Y+𝟙) → ⌜ e ⌝ (inr *) ≡ inr *)
       ≃ (X+𝟙 ≃ Y+𝟙)
 step₃ = φ , (γ , η) , (γ , ε)
  where
   A = co-derived-set (Y+𝟙) × Σ \(e : X+𝟙 ≃ Y+𝟙) → ⌜ e ⌝ (inr *) ≡ inr *
   B = X+𝟙 ≃ Y+𝟙

   φ : A → B
   φ ((t , i) , ((f , j) , p)) = g , k
    where
     g : X+𝟙 → Y+𝟙
     g = swap t (inr *) i new-point-is-isolated ∘ f
     k : is-equiv g
     k = ∘-is-equiv-abstract j (swap-is-equiv t (inr *) i new-point-is-isolated)

   γ : B → A
   γ (g , k) = (t , i) , ((f , j) , p)
    where
     t : Y+𝟙
     t = g (inr *)
     i : is-isolated t
     i = equivs-preserve-isolatedness g k (inr *) new-point-is-isolated
     f : X+𝟙 → Y+𝟙
     f = swap t (inr *) i new-point-is-isolated ∘ g
     j : is-equiv f
     j = ∘-is-equiv-abstract k (swap-is-equiv t (inr *) i new-point-is-isolated)
     p : f (inr *) ≡ inr *
     p = swap-equation₀ t (inr *) i new-point-is-isolated

   η : φ ∘ γ ∼ id
   η (g , k) = r
    where
     z : Y+𝟙
     z = g (inr *)
     i : is-isolated z
     i = equivs-preserve-isolatedness g k (inr *) new-point-is-isolated
     h : (swap (g (inr *)) (inr *) i new-point-is-isolated)
       ∘ (swap (g (inr *)) (inr *) i new-point-is-isolated)
       ∘ g
       ∼ g
     h = swap-involutive z (inr *) i new-point-is-isolated ∘ g
     r : φ (γ (g , k)) ≡ (g , k)
     r = to-Σ-≡ (dfunext (fe _ _) h , being-equiv-is-a-prop fe g _ k)

   ε : γ ∘ φ ∼ id
   ε ((t , i) , ((f , j) , p)) = s
    where
     g : X+𝟙 → Y+𝟙
     g = swap t (inr *) i new-point-is-isolated ∘ f

     k : is-equiv g
     k = ∘-is-equiv-abstract j (swap-is-equiv t (inr *) i new-point-is-isolated)

     l : is-isolated (g (inr *))
     l = equivs-preserve-isolatedness g k (inr *) new-point-is-isolated

     q : g (inr *) ≡ t
     q = g (inr *)                                      ≡⟨ a ⟩
         swap t (inr *) i new-point-is-isolated (inr *) ≡⟨ b ⟩
         t                                              ∎
      where
       a = ap (swap t (inr *) i new-point-is-isolated) p
       b = swap-equation₁ t (inr *) i new-point-is-isolated

     r : (g (inr *) , l) ≡ (t , i)
     r = to-subtype-≡ (being-isolated-is-a-prop fe) q

     f' : X+𝟙 → Y+𝟙
     f' = swap (g (inr *)) (inr *) l new-point-is-isolated ∘ g

     j' : is-equiv f'
     j' = ∘-is-equiv-abstract k (swap-is-equiv (g (inr *)) (inr *) l new-point-is-isolated)

     h : f' ∼ f
     h z = swap (g (inr *)) (inr *) l new-point-is-isolated
            (swap t (inr *) i new-point-is-isolated (f z))    ≡⟨ a ⟩

           swap t (inr *) i new-point-is-isolated
            (swap t (inr *) i new-point-is-isolated (f z))    ≡⟨ b ⟩

           f z                                                ∎
      where
       ψ : co-derived-set (Y+𝟙) → Y+𝟙
       ψ (t' , i') = swap t' (inr *) i' new-point-is-isolated
                      (swap t (inr *) i new-point-is-isolated (f z))
       a = ap ψ r
       b = swap-involutive t (inr *) i new-point-is-isolated (f z)

     m : is-isolated (f (inr *))
     m = equivs-preserve-isolatedness f j (inr *) new-point-is-isolated

     n : {t : Y+𝟙} → is-prop (f (inr *) ≡ t)
     n = isolated-is-h-isolated (f (inr *)) m

     o : f' , j' ≡ f , j
     o = to-subtype-≡ (being-equiv-is-a-prop fe) (dfunext (fe _ _) h)

     p' : f' (inr *) ≡ inr *
     p' = swap-equation₀ (g (inr *)) (inr *) l new-point-is-isolated

     s : ((g (inr *) , l) , ((f' , j') , p')) ≡ ((t , i) , ((f , j) , p))
     s = to-×-≡ r (to-Σ-≡ (o , n top' p))
      where
       top' = transport (λ - → ⌜ - ⌝ (inr *) ≡ inr *) o p'

 step₄ : co-derived-set (Y+𝟙) × (X ≃ Y) ≃ (X+𝟙 ≃ Y+𝟙)
 step₄ = step₂ ● step₃

\end{code}

This is the end of the submodule, which has the following corollaries:

\begin{code}

Aut : 𝓤 ̇ → 𝓤 ̇
Aut X = (X ≃ X)

general-factorial : (X : 𝓤 ̇ ) → co-derived-set (X + 𝟙) × Aut X ≃ Aut(X + 𝟙)
general-factorial {𝓤} X = factorial-steps.step₄ 𝓤 𝓤 X X

discrete-factorial : (X : 𝓤 ̇ )
                   → is-discrete X
                   → (X + 𝟙) × Aut X ≃ Aut (X + 𝟙)
discrete-factorial X d = γ
 where
 i = ×cong (≃-sym (≃-cods (X + 𝟙) ( +discrete d 𝟙-is-discrete))) (≃-refl (Aut X))

 γ = (X + 𝟙) × Aut X                ≃⟨ i                   ⟩
     co-derived-set (X + 𝟙) × Aut X ≃⟨ general-factorial X ⟩
     Aut (X + 𝟙)                    ■

perfect-factorial : (X : 𝓤 ̇ )
                  → is-perfect X
                  → Aut X ≃ Aut (X + 𝟙)
perfect-factorial X i =
  Aut X                          ≃⟨ ≃-sym (𝟙-lneutral {universe-of X} {universe-of X})                               ⟩
  𝟙 × Aut X                      ≃⟨ ×cong (≃-sym (singleton-≃-𝟙 (perfect-coderived-singleton X i))) (≃-refl (Aut X)) ⟩
  co-derived-set (X + 𝟙) × Aut X ≃⟨ general-factorial X                                                              ⟩
  Aut (X + 𝟙)                    ■

\end{code}

Exercise. Conclude that the map (-)+𝟙 : 𝓤 ̇ → 𝓤 ̇, although it is
left-cancellable, is not an embedding, but that it is an embedding
when restricted to perfect types.

We should not forget the (trivial) "base case":

\begin{code}

factorial-base : 𝟙 {𝓥} ≃ Aut (𝟘 {𝓤})
factorial-base = f , ((g , η) , (g , ε))
 where
  f : 𝟙 → Aut 𝟘
  f _ = id , ((id , (λ _ → refl)) , (id , (λ _ → refl)))
  g : Aut 𝟘 → 𝟙
  g = unique-to-𝟙
  η : (e : Aut 𝟘) → f (g e) ≡ e
  η _ = to-subtype-≡ (being-equiv-is-a-prop fe) (dfunext (fe _ _) (λ y → 𝟘-elim y))
  ε : (x : 𝟙) → g (f x) ≡ x
  ε * = refl

\end{code}
