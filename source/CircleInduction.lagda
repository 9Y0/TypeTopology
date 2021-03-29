Tom de Jong, 1-18 March 2021

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons


module CircleInduction where

𝓛 : (X : 𝓤 ̇ ) → 𝓤 ̇
𝓛 X = Σ x ꞉ X , x ≡ x

𝓛-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → 𝓛 X → 𝓛 Y
𝓛-functor f (x , p) = f x , ap f p

{-
𝓛-functor-id : {X : 𝓤 ̇ } → 𝓛-functor id ∼ id {𝓤} {𝓛 X}
𝓛-functor-id {𝓤} {X} (x , p) = to-Σ-≡ (refl , γ p)
 where
  γ : {y z : X} (q : y ≡ z) → transport (λ - → y ≡ -) q refl ≡ q
  γ refl = refl

𝓛-functor-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
               → 𝓛-functor g ∘ 𝓛-functor f ∼ 𝓛-functor (g ∘ f)
𝓛-functor-comp f g (x , p) = to-Σ-≡ (refl , (ap-ap f g p))
-}

\end{code}

\begin{code}

module _
        (𝕊¹ : 𝓤 ̇ )
        (base : 𝕊¹)
        (loop : base ≡ base)
       where

 𝕊¹-universal-map : (A : 𝓥 ̇ )
                  → (𝕊¹ → A) → 𝓛 A
 𝕊¹-universal-map A f = (f base , ap f loop)

 \end{code}

 \begin{code}

 module _
         (𝕊¹-universal-property : {𝓥 : Universe} (A : 𝓥 ̇ )
                                → is-equiv (𝕊¹-universal-map A))
        where

  𝕊¹-uniqueness-principle : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                          → ∃! r ꞉ (𝕊¹ → A) , (r base , ap r loop) ≡ (a , p)
  𝕊¹-uniqueness-principle {𝓥} {A} a p =
    equivs-are-vv-equivs (𝕊¹-universal-map A)
                         (𝕊¹-universal-property A) (a , p)

  𝕊¹-at-most-one-function : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                          → is-prop (Σ r ꞉ (𝕊¹ → A) , (r base , ap r loop) ≡ (a , p))
  𝕊¹-at-most-one-function a p = singletons-are-props (𝕊¹-uniqueness-principle a p)

  𝕊¹-rec : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
         → 𝕊¹ → A
  𝕊¹-rec {𝓥} {A} a p = ∃!-witness (𝕊¹-uniqueness-principle a p)

  𝕊¹-rec-comp : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
              → 𝓛-functor (𝕊¹-rec a p) (base , loop) ≡[ 𝓛 A ] (a , p)
  𝕊¹-rec-comp {𝓥} {A} a p = ∃!-is-witness (𝕊¹-uniqueness-principle a p)

  𝕊¹-rec-on-base : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                  → 𝕊¹-rec a p base ≡ a
  𝕊¹-rec-on-base a p = ap pr₁ (𝕊¹-rec-comp a p)

  𝕊¹-rec-on-loop : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                 → transport (λ - → - ≡ -) (𝕊¹-rec-on-base a p)
                     (ap (𝕊¹-rec a p) loop)
                 ≡ p
  𝕊¹-rec-on-loop a p = from-Σ-≡' (𝕊¹-rec-comp a p)

\end{code}

\begin{code}

  𝕊¹-uniqueness-principle-comp : {A : 𝓥 ̇ } (a : A) (p : a ≡ a) (f g : 𝕊¹ → A)
                                 (u : 𝓛-functor f (base , loop) ≡ (a , p))
                                 (v : 𝓛-functor g (base , loop) ≡ (a , p))
                               → ap (λ - → 𝓛-functor - (base , loop))
                                  (ap pr₁ (𝕊¹-at-most-one-function a p
                                            (f , u) (g , v)))
                               ≡ u ∙ v ⁻¹
  𝕊¹-uniqueness-principle-comp a p f g u v = γ u v (𝕊¹-at-most-one-function a p (f , u) (g , v))
   where
    γ : (u : 𝓛-functor f (base , loop) ≡ (a , p))
        (v : 𝓛-functor g (base , loop) ≡ (a , p))
        (w : (f , u) ≡ (g , v))
      → ap (λ - → 𝓛-functor - (base , loop)) (ap pr₁ w) ≡ u ∙ v ⁻¹
    γ refl v refl = refl

  𝕊¹-uniqueness-principle-comp₁ : {A : 𝓥 ̇ } (a : A) (p : a ≡ a) (f g : 𝕊¹ → A)
                                  (u : 𝓛-functor f (base , loop) ≡ (a , p))
                                  (v : 𝓛-functor g (base , loop) ≡ (a , p))
                                → happly (ap pr₁ (𝕊¹-at-most-one-function a p
                                                   (f , u) (g , v))) base
                                ≡ (ap pr₁ u) ∙ (ap pr₁ v) ⁻¹
  𝕊¹-uniqueness-principle-comp₁ a p f g u v = γ
   where
    σ : (f , u) ≡ (g , v)
    σ = 𝕊¹-at-most-one-function a p (f , u) (g , v)
    γ = happly (ap pr₁ σ) base                                   ≡⟨ I   ⟩
        ap pr₁ (ap (λ - → 𝓛-functor - (base , loop)) (ap pr₁ σ)) ≡⟨ II  ⟩
        ap pr₁ (u ∙ v ⁻¹)                                        ≡⟨ III ⟩
        ap pr₁ u ∙ ap pr₁ (v ⁻¹)                                 ≡⟨ IV  ⟩
        ap pr₁ u ∙ ap pr₁ v ⁻¹                                   ∎
     where
      I   = (ap-ap (λ - → 𝓛-functor - (base , loop)) pr₁ (ap pr₁ σ)) ⁻¹
      II  = ap (ap pr₁) (𝕊¹-uniqueness-principle-comp a p f g u v)
      III = ap-∙ pr₁ u (v ⁻¹)
      IV  = ap (_∙_ (ap pr₁ u)) ((ap-sym pr₁ v) ⁻¹)

\end{code}

\begin{code}

  module 𝕊¹-induction
          (A : 𝕊¹ → 𝓥 ̇ )
          (a : A base)
          (l : transport A loop a ≡ a)
         where

   l⁺ : (base , a) ≡[ Σ A ] (base , a)
   l⁺ = to-Σ-≡ (loop , l)

   r : 𝕊¹ → Σ A
   r = 𝕊¹-rec (base , a) l⁺

   𝕊¹-induction-key-≡ : ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop)
                      ≡[ 𝓛 𝕊¹ ] (base , loop)
   𝕊¹-induction-key-≡ =
    ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop) ≡⟨ I   ⟩
    𝓛-functor pr₁ (r base , ap r loop)   ≡⟨ II  ⟩
    (base , ap pr₁ (to-Σ-≡ (loop , l)))  ≡⟨ III ⟩
    (base , loop)                        ∎
     where
      I   = to-Σ-≡ (refl , ((ap-ap r pr₁ loop) ⁻¹))
      II  = ap (𝓛-functor pr₁) (𝕊¹-rec-comp (base , a) l⁺)
      III = to-Σ-≡ (refl , (ap-pr₁-to-Σ-≡ (loop , l)))

   𝕊¹-induction-key-lemma : pr₁ ∘ r ≡ id
   𝕊¹-induction-key-lemma = ap pr₁ (𝕊¹-at-most-one-function base loop
                                     (pr₁ ∘ r , 𝕊¹-induction-key-≡)
                                     (id , to-Σ-≡ (refl , ap-id-is-id loop)))

   𝕊¹-induction : (x : 𝕊¹) → A x
   𝕊¹-induction x = transport A (happly 𝕊¹-induction-key-lemma x) (pr₂ (r x))

\end{code}

\begin{code}

   pr₁-𝕊¹-induction-key-≡ : ap pr₁ 𝕊¹-induction-key-≡
                          ≡ ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)
   pr₁-𝕊¹-induction-key-≡ =
    ap pr₁ 𝕊¹-induction-key-≡    ≡⟨ I    ⟩
    ap pr₁ (κ₁ ∙ (κ₂ ∙ κ₃))      ≡⟨ II   ⟩
    ap pr₁ κ₁ ∙ ap pr₁ (κ₂ ∙ κ₃) ≡⟨ III  ⟩
    refl ∙ ap pr₁ (κ₂ ∙ κ₃)      ≡⟨ IV   ⟩
    ap pr₁ (κ₂ ∙ κ₃)             ≡⟨ V    ⟩
    ap pr₁ κ₂ ∙ ap pr₁ κ₃        ≡⟨ VI   ⟩
    ap pr₁ κ₂ ∙ refl             ≡⟨ refl ⟩
    ap pr₁ κ₂                    ≡⟨ VII  ⟩
    ap (pr₁ ∘ 𝓛-functor pr₁) c   ≡⟨ refl ⟩
    ap (pr₁ ∘ pr₁) c             ≡⟨ VIII ⟩
    ap pr₁ (ap pr₁ c)            ≡⟨ refl ⟩
    ap pr₁ b                     ∎
    where
     b = 𝕊¹-rec-on-base (base , a) l⁺
     c = 𝕊¹-rec-comp (base , a) l⁺
     κ₁ = to-Σ-≡ (refl , ((ap-ap r pr₁ loop) ⁻¹))
     κ₂ = ap (𝓛-functor pr₁) c
     κ₃ = to-Σ-≡ (refl , (ap-pr₁-to-Σ-≡ (loop , l)))
     I   = ap (ap pr₁) e
      where
       e : 𝕊¹-induction-key-≡ ≡ κ₁ ∙ (κ₂ ∙ κ₃)
       e = refl
     II  = ap-∙ pr₁ κ₁ (κ₂ ∙ κ₃)
     III = ap (_∙ (ap pr₁ (κ₂ ∙ κ₃)))
            (ap-pr₁-to-Σ-≡ {𝓤} {𝓤} {𝕊¹} {λ - → (- ≡ -)} {_} {_}
             (refl , ((ap-ap r pr₁ loop) ⁻¹)))
     IV  = refl-left-neutral
     V   = ap-∙ pr₁ κ₂ κ₃
     VI  = ap ((ap pr₁ κ₂) ∙_)
            (ap-pr₁-to-Σ-≡ {𝓤} {𝓤} {𝕊¹} {λ - → (- ≡ -)} {_} {_}
             (refl , ap-pr₁-to-Σ-≡ (loop , l)))
     VII = ap-ap (𝓛-functor pr₁) pr₁ c
     VIII = (ap-ap pr₁ pr₁ c) ⁻¹

   ρ : 𝕊¹ → Σ A
   ρ x = (x , 𝕊¹-induction x)

   r-comp : (r base , ap r loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
   r-comp = 𝕊¹-rec-comp (base , a) l⁺

   ρ-r-homotopy : ρ ∼ r
   ρ-r-homotopy x = to-Σ-≡ ((γ₁ ⁻¹) , γ₂)
    where
     γ₁ : pr₁ (r x) ≡ pr₁ (ρ x)
     γ₁ = happly 𝕊¹-induction-key-lemma x
     γ₂ = transport A (γ₁ ⁻¹) (pr₂ (ρ x))                  ≡⟨ refl ⟩
          transport A (γ₁ ⁻¹) (transport A γ₁ (pr₂ (r x))) ≡⟨ I    ⟩
          transport A (γ₁ ∙ γ₁ ⁻¹) (pr₂ (r x))             ≡⟨ II   ⟩
          transport A refl (pr₂ (r x))                     ≡⟨ refl ⟩
          pr₂ (r x)                                        ∎
      where
       I  = (transport-comp A γ₁ (γ₁ ⁻¹)) ⁻¹
       II = ap (λ - → transport A - (pr₂ (r x))) ((right-inverse γ₁) ⁻¹)

   ρ-and-r-on-base-and-loop : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] (r base , ap r loop)
   ρ-and-r-on-base-and-loop = to-Σ-≡ (ρ-r-homotopy base , γ)
    where
     γ = transport (λ - → - ≡ -) (ρ-r-homotopy base) (ap ρ loop) ≡⟨ I  ⟩
         ρ-r-homotopy base ⁻¹ ∙ ap ρ loop ∙ ρ-r-homotopy base    ≡⟨ II ⟩
         ap r loop                                               ∎
      where
       I  = transport-along-≡ (ρ-r-homotopy base) (ap ρ loop)
       II = homotopies-are-natural'' ρ r ρ-r-homotopy {base} {base} {loop}

   ρ-comp : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
   ρ-comp = ρ-and-r-on-base-and-loop ∙ r-comp

   r-comp-lemma : ap (pr₁ ∘ pr₁) r-comp ≡ happly 𝕊¹-induction-key-lemma base
   r-comp-lemma = γ ⁻¹
    where
     κ = 𝕊¹-induction-key-≡
     γ = happly 𝕊¹-induction-key-lemma base                    ≡⟨ I    ⟩
         ap pr₁ κ ∙ ap π (to-Σ-≡ (refl , ap-id-is-id loop)) ⁻¹ ≡⟨ II   ⟩
         ap pr₁ κ ∙ refl ⁻¹                                    ≡⟨ refl ⟩
         ap pr₁ κ                                              ≡⟨ III  ⟩
         ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)                 ≡⟨ refl ⟩
         ap pr₁ (ap pr₁ r-comp)                                ≡⟨ IV   ⟩
         ap (pr₁ ∘ pr₁) r-comp                                 ∎
      where
       π : 𝓛 (𝕊¹) → 𝕊¹
       π = pr₁
       I   = 𝕊¹-uniqueness-principle-comp₁ base loop (pr₁ ∘ r) id κ
              (to-Σ-≡ (refl , (ap-id-is-id loop)))
       II  = ap (λ - → ap pr₁ κ ∙ - ⁻¹)
              (ap-pr₁-to-Σ-≡ {𝓤} {𝓤} {𝕊¹} {λ - → (- ≡ -)} {_} {_}
               (refl , ap-id-is-id loop))
       III = pr₁-𝕊¹-induction-key-≡
       IV  = ap-ap pr₁ pr₁ r-comp

   ρ-comp-lemma : ap pr₁ (ap pr₁ ρ-comp) ≡ refl
   ρ-comp-lemma =
    ap pr₁ (ap pr₁ ρ-comp)                                          ≡⟨ I   ⟩
    ap (pr₁ ∘ pr₁) ρ-comp                                           ≡⟨ II  ⟩
    ap (pr₁ ∘ pr₁) ρ-and-r-on-base-and-loop ∙ ap (pr₁ ∘ pr₁) r-comp ≡⟨ III ⟩
    p ⁻¹ ∙ p                                                        ≡⟨ IV  ⟩
    refl                                                            ∎
    where
     p = happly 𝕊¹-induction-key-lemma base
     I   = ap-ap pr₁ pr₁ ρ-comp
     II  = ap-∙ (pr₁ ∘ pr₁) ρ-and-r-on-base-and-loop r-comp
     IV  = left-inverse p
     III = ap₂ _∙_ γ₁ γ₂
      where
       γ₁ : ap (pr₁ ∘ pr₁) ρ-and-r-on-base-and-loop  ≡ p ⁻¹
       γ₁ = ap (pr₁ ∘ pr₁) ρ-and-r-on-base-and-loop  ≡⟨ I₁   ⟩
            ap pr₁ (ap pr₁ ρ-and-r-on-base-and-loop) ≡⟨ II₁  ⟩
            ap pr₁ (ρ-r-homotopy base)               ≡⟨ III₁ ⟩
            p ⁻¹                                     ∎
        where
         I₁   = (ap-ap pr₁ pr₁ ρ-and-r-on-base-and-loop) ⁻¹
         II₁  = ap (ap pr₁) (ap-pr₁-to-Σ-≡ (ρ-r-homotopy base , _))
         III₁ = ap-pr₁-to-Σ-≡ ((p ⁻¹) , _)
       γ₂ : ap (pr₁ ∘ pr₁) r-comp ≡ p
       γ₂ = ϕ ⁻¹
        where
         κ = 𝕊¹-induction-key-≡
         ϕ = p                                                     ≡⟨ I₂    ⟩
             ap pr₁ κ ∙ ap π (to-Σ-≡ (refl , ap-id-is-id loop)) ⁻¹ ≡⟨ II₂   ⟩
             ap pr₁ κ ∙ refl ⁻¹                                    ≡⟨ refl  ⟩
             ap pr₁ κ                                              ≡⟨ III₂  ⟩
             ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)                 ≡⟨ refl  ⟩
             ap pr₁ (ap pr₁ r-comp)                                ≡⟨ IV₂   ⟩
             ap (pr₁ ∘ pr₁) r-comp                                 ∎
          where
           π : 𝓛 (𝕊¹) → 𝕊¹
           π = pr₁
           I₂   = 𝕊¹-uniqueness-principle-comp₁ base loop (pr₁ ∘ r) id κ
                   (to-Σ-≡ (refl , (ap-id-is-id loop)))
           II₂  = ap (λ - → ap pr₁ κ ∙ - ⁻¹)
                   (ap-pr₁-to-Σ-≡ {𝓤} {𝓤} {𝕊¹} {λ - → (- ≡ -)} {_} {_}
                    (refl , ap-id-is-id loop))
           III₂ = pr₁-𝕊¹-induction-key-≡
           IV₂  = ap-ap pr₁ pr₁ r-comp

   𝕊¹-induction-on-base : 𝕊¹-induction base ≡ a
   𝕊¹-induction-on-base =
    transport (λ - → transport A - (𝕊¹-induction base) ≡ a) ρ-comp-lemma γ
     where
      γ : transport A (ap pr₁ (ap pr₁ ρ-comp)) (𝕊¹-induction base) ≡ a
      γ = from-Σ-≡' (ap pr₁ ρ-comp)

   𝕊¹-induction-on-loop-lemma : (loop , transport (λ - → transport A loop - ≡ -)
                                         𝕊¹-induction-on-base
                                         (apd 𝕊¹-induction loop))
                              ≡ (loop , l)
   𝕊¹-induction-on-loop-lemma =
      (fromto-Σ-≡ (loop , transport (λ - → transport A loop - ≡ -) σ τ)) ⁻¹
    ∙ (ap from-Σ-≡ γ) ∙ (fromto-Σ-≡ (loop , l))
     where
      σ = 𝕊¹-induction-on-base
      τ = apd 𝕊¹-induction loop
      γ : to-Σ-≡ (loop , transport (λ - → transport A loop - ≡ -) σ τ)
        ≡ to-Σ-≡ (loop , l)
      γ = to-Σ-≡ (loop , transport (λ - → transport A loop - ≡ -) σ τ)    ≡⟨ I   ⟩
          transport (λ - → - ≡ -) (to-Σ-≡ (refl , σ)) (to-Σ-≡ (loop , τ)) ≡⟨ II  ⟩
          transport (λ - → - ≡ -) (ap pr₁ ρ-comp) (to-Σ-≡ (loop , τ))     ≡⟨ III ⟩
          transport (λ - → - ≡ -) (ap pr₁ ρ-comp) (ap ρ loop)             ≡⟨ IV  ⟩
          to-Σ-≡ (loop , l)                                               ∎
       where
        I   = h loop σ τ
         where
          h : {X : 𝓦 ̇ } {Y : X → 𝓣 ̇ } {x : X} (p : x ≡ x) {y y' : Y x}
              (q : y ≡ y') (q' : transport Y p y ≡ y)
            → to-Σ-≡ (p , transport (λ - → transport Y p - ≡ -) q q')
            ≡ transport (λ - → - ≡ -) (to-Σ-≡ (refl , q)) (to-Σ-≡ (p , q'))
          h p refl q' = refl
        II  = ap (λ - → transport (λ - → - ≡ -) - (to-Σ-≡ (loop , τ))) h
         where
          h = to-Σ-≡ (refl , σ)                 ≡⟨ I'  ⟩
              to-Σ-≡ (from-Σ-≡ (ap pr₁ ρ-comp)) ≡⟨ II' ⟩
              ap pr₁ ρ-comp                     ∎
           where
            I'  = (ap to-Σ-≡ (to-Σ-≡ (ρ-comp-lemma , refl))) ⁻¹
            II' = tofrom-Σ-≡ (ap pr₁ ρ-comp)
        III = ap (transport (λ - → - ≡ -) (ap pr₁ ρ-comp)) (h 𝕊¹-induction loop)
         where
          h : {X : 𝓦 ̇ } {Y : X → 𝓣 ̇ } (f : (x : X) → Y x)
              {x x' : X} (p : x ≡ x')
            → to-Σ-≡ (p , apd f p) ≡ ap (λ x → (x , f x)) p
          h f refl = refl
        IV  = from-Σ-≡' ρ-comp

   module _
           (base-sethood : is-set (base ≡ base))
          where

    𝕊¹-induction-on-loop : transport (λ - → transport A loop - ≡ -)
                            𝕊¹-induction-on-base (apd 𝕊¹-induction loop)
                         ≡ l
    𝕊¹-induction-on-loop =
     ap-pr₁-refl-lemma (λ - → transport A - a ≡ a) 𝕊¹-induction-on-loop-lemma γ
     where
      γ : ap pr₁ 𝕊¹-induction-on-loop-lemma ≡ refl
      γ = base-sethood (ap pr₁ 𝕊¹-induction-on-loop-lemma) refl
      t : transport A loop a ≡ a
      t = transport (λ - → transport A loop - ≡ -)
           𝕊¹-induction-on-base (apd 𝕊¹-induction loop)

    𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
                      ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
    𝕊¹-induction-comp = to-Σ-≡ (𝕊¹-induction-on-base , 𝕊¹-induction-on-loop)


  open import Integers
  open import Integers-Properties

  open import UF-Univalence

  module _
          (ua : is-univalent 𝓤₀)
         where

   succ-ℤ-≡ : ℤ ≡ ℤ
   succ-ℤ-≡ = eqtoid ua ℤ ℤ succ-ℤ-≃

   code : 𝕊¹ → 𝓤₀ ̇
   code = 𝕊¹-rec ℤ succ-ℤ-≡

   code-on-base : code base ≡ ℤ
   code-on-base = 𝕊¹-rec-on-base ℤ succ-ℤ-≡

   ℤ-to-code-base : ℤ → code base
   ℤ-to-code-base = Idtofun (code-on-base ⁻¹)

   code-base-to-ℤ : code base → ℤ
   code-base-to-ℤ = Idtofun code-on-base

   transport-code-loop-is-succ-ℤ : code-base-to-ℤ
                                 ∘ transport code loop
                                 ∘ ℤ-to-code-base
                                 ≡ succ-ℤ
   transport-code-loop-is-succ-ℤ =
    δ ∘ transport code loop ∘ ε                  ≡⟨ I    ⟩
    δ ∘ transport id acl ∘ ε                     ≡⟨ refl ⟩
    Idtofun cob ∘ Idtofun acl ∘ Idtofun (cob ⁻¹) ≡⟨ II   ⟩
    Idtofun cob ∘ Idtofun (cob ⁻¹ ∙ acl)         ≡⟨ III  ⟩
    Idtofun (cob ⁻¹ ∙ acl ∙ cob)                 ≡⟨ IV   ⟩
    Idtofun succ-ℤ-≡                             ≡⟨ V    ⟩
    succ-ℤ                                       ∎
     where
      cob = code-on-base
      acl = ap code loop
      ε = ℤ-to-code-base
      δ = code-base-to-ℤ
      I   = ap (λ - → δ ∘ - ∘ ε) (transport-ap' id code loop)
      II  = ap (_∘_ (Idtofun cob)) ((Idtofun-∙ ua (cob ⁻¹) acl) ⁻¹)
      III = (Idtofun-∙ ua (cob ⁻¹ ∙ acl) cob) ⁻¹
      IV  = ap Idtofun ((transport-along-≡ cob acl) ⁻¹
                       ∙ (𝕊¹-rec-on-loop ℤ succ-ℤ-≡))
      V   = Idtofun-eqtoid ua succ-ℤ-≃

   transport-code-loop⁻¹-is-pred-ℤ : code-base-to-ℤ
                                   ∘ transport code (loop ⁻¹)
                                   ∘ ℤ-to-code-base
                                   ∼ pred-ℤ
   transport-code-loop⁻¹-is-pred-ℤ x = equivs-are-lc succ-ℤ succ-ℤ-is-equiv γ
    where
     γ : (succ-ℤ ∘ code-base-to-ℤ ∘ transport code (loop ⁻¹) ∘ ℤ-to-code-base) x
       ≡ (succ-ℤ ∘ pred-ℤ) x
     γ = (succ-ℤ ∘ δ ∘ t⁻¹ ∘ ε) x    ≡⟨ I   ⟩
         (δ ∘ t ∘ ε ∘ δ ∘ t⁻¹ ∘ ε) x ≡⟨ II  ⟩
         (δ ∘ t ∘ t⁻¹ ∘ ε) x         ≡⟨ III ⟩
         (δ ∘ ε) x                   ≡⟨ IV  ⟩
         x                           ≡⟨ V   ⟩
         (succ-ℤ ∘ pred-ℤ) x         ∎
      where
       ε = ℤ-to-code-base
       δ = code-base-to-ℤ
       t⁻¹ = transport code (loop ⁻¹)
       t   = transport code loop
       I   = happly (transport-code-loop-is-succ-ℤ ⁻¹) ((δ ∘ t⁻¹ ∘ ε) x)
       II  = ap (δ ∘ t) (Idtofun-section code-on-base (t⁻¹ (ε x)))
       III = ap δ (back-and-forth-transport loop)
       IV  = Idtofun-retraction code-on-base x
       V   = (succ-ℤ-is-retraction x) ⁻¹

   transport-code-loop⁻¹-is-pred-ℤ' : transport code (loop ⁻¹)
                                    ∼ ℤ-to-code-base ∘ pred-ℤ ∘ code-base-to-ℤ
   transport-code-loop⁻¹-is-pred-ℤ' x =
    transport code (loop ⁻¹) x                   ≡⟨ I   ⟩
    (ε ∘ δ ∘ transport code (loop ⁻¹)) x         ≡⟨ II  ⟩
    (ε ∘ δ ∘ transport code (loop ⁻¹) ∘ ε ∘ δ) x ≡⟨ III ⟩
    (ε ∘ pred-ℤ ∘ δ) x                           ∎
     where
      ε = ℤ-to-code-base
      δ = code-base-to-ℤ
      I   = (Idtofun-section code-on-base (transport code (loop ⁻¹) x)) ⁻¹
      II  = ap (ε ∘ δ ∘ transport code (loop ⁻¹))
             ((Idtofun-section code-on-base x) ⁻¹)
      III = ap ε (transport-code-loop⁻¹-is-pred-ℤ (δ x))

   encode : (x : 𝕊¹) → (base ≡ x) → code x
   encode x p = transport code p (ℤ-to-code-base 𝟎)

   iterated-path : {X : 𝓦 ̇ } {x : X} → x ≡ x → ℕ → x ≡ x
   iterated-path p zero     = refl
   iterated-path p (succ n) = p ∙ iterated-path p n

   iterated-path-comm : {X : 𝓦 ̇ } {x : X} (p : x ≡ x) (n : ℕ)
                      → iterated-path p n ∙ p ≡ p ∙ iterated-path p n
   iterated-path-comm p zero = refl ∙ p ≡⟨ refl-left-neutral ⟩
                               p        ≡⟨ refl              ⟩
                               p ∙ refl ∎
   iterated-path-comm p (succ n) = p ∙ iterated-path p n ∙ p   ≡⟨ I  ⟩
                                   p ∙ (iterated-path p n ∙ p) ≡⟨ II ⟩
                                   p ∙ (p ∙ iterated-path p n) ∎
    where
     I  =  ∙assoc p (iterated-path p n) p
     II = ap (p ∙_) (iterated-path-comm p n)

   loops : ℤ → base ≡ base
   loops 𝟎       = refl
   loops (pos n) = iterated-path loop (succ n)
   loops (neg n) = iterated-path (loop ⁻¹) (succ n)

   module _
           (fe : funext 𝓤₀ 𝓤)
          where

    open import UF-Lower-FunExt

    loops-lemma : (_∙ loop) ∘ loops ∘ pred-ℤ ≡ loops
    loops-lemma = dfunext fe h
     where
      h : (k : ℤ) → loops (pred-ℤ k) ∙ loop ≡ loops k
      h 𝟎 = loop ⁻¹ ∙ refl ∙ loop ≡⟨ refl              ⟩
            loop ⁻¹ ∙ loop        ≡⟨ left-inverse loop ⟩
            refl                  ∎
      h (pos n) = g n
       where
        g : (n : ℕ) → loops (pred-ℤ (pos n)) ∙ loop ≡ loops (pos n)
        g zero     = iterated-path-comm loop zero
        g (succ n) = iterated-path-comm loop (succ n)
      h (neg n) =
       loop ⁻¹ ∙ (loop ⁻¹ ∙ iterated-path (loop ⁻¹) n) ∙ loop ≡⟨ I'   ⟩
       loop ⁻¹ ∙ (iterated-path (loop ⁻¹) n ∙ loop ⁻¹) ∙ loop ≡⟨ II'  ⟩
       loop ⁻¹ ∙ iterated-path (loop ⁻¹) n ∙ (loop ⁻¹ ∙ loop) ≡⟨ III' ⟩
       loop ⁻¹ ∙ iterated-path (loop ⁻¹) n                    ∎
        where
         I'   = ap (λ - → loop ⁻¹ ∙ - ∙ loop)
                 ((iterated-path-comm (loop ⁻¹) n) ⁻¹)
         II'  = ∙assoc (loop ⁻¹) (iterated-path (loop ⁻¹) n ∙ loop ⁻¹) loop
              ∙ ap (loop ⁻¹ ∙_)
                 (∙assoc (iterated-path (loop ⁻¹) n) (loop ⁻¹) loop)
              ∙ (∙assoc (loop ⁻¹) (iterated-path (loop ⁻¹) n)
                  (loop ⁻¹ ∙ loop)) ⁻¹
         III' = ap ((loop ⁻¹ ∙ iterated-path (loop ⁻¹) n) ∙_)
                 (left-inverse loop)

    l : transport (λ - → code - → base ≡ -) loop (loops ∘ code-base-to-ℤ)
      ≡ (loops ∘ code-base-to-ℤ)
    l = transport (λ - → code - → base ≡ -) loop f                     ≡⟨ I   ⟩
        transport (λ - → base ≡ -) loop ∘ f ∘ transport code (loop ⁻¹) ≡⟨ II  ⟩
        (_∙ loop) ∘ f ∘ transport code (loop ⁻¹)                       ≡⟨ III ⟩
        (_∙ loop) ∘ loops ∘ δ ∘ ε ∘ pred-ℤ ∘ δ                         ≡⟨ IV  ⟩
        (_∙ loop) ∘ loops ∘ pred-ℤ ∘ δ                                 ≡⟨ V   ⟩
        loops ∘ δ                                                      ∎
     where
      ε : ℤ → code base
      ε = ℤ-to-code-base
      δ : code base → ℤ
      δ = code-base-to-ℤ
      f : code base → base ≡ base
      f = loops ∘ δ
      I   = transport-along-→ code (_≡_ base) loop f
      II  = refl
      III = ap ((_∙ loop) ∘ f ∘_)
             (dfunext (lower-funext 𝓤₀ 𝓤 fe) transport-code-loop⁻¹-is-pred-ℤ')
      IV  = ap (λ - → (_∙ loop) ∘ loops ∘ - ∘ pred-ℤ ∘ δ)
             (dfunext (lower-funext 𝓤₀ 𝓤 fe) (Idtofun-retraction code-on-base))
      V   = ap (_∘ δ) loops-lemma


    open 𝕊¹-induction (λ - → code - → base ≡ -) (loops ∘ code-base-to-ℤ) l

    decode : (x : 𝕊¹) → code x → base ≡ x
    decode = 𝕊¹-induction

    decode-encode : (x : 𝕊¹) (p : base ≡ x) → decode x (encode x p) ≡ p
    decode-encode base refl =
     decode base (encode base refl)                       ≡⟨ refl ⟩
     decode base (transport code refl (ℤ-to-code-base 𝟎)) ≡⟨ refl ⟩
     decode base (ℤ-to-code-base 𝟎)                       ≡⟨ I    ⟩
     loops (code-base-to-ℤ (ℤ-to-code-base 𝟎))            ≡⟨ II   ⟩
     loops 𝟎                                              ≡⟨ refl ⟩
     refl                                                 ∎
      where
       I  = happly 𝕊¹-induction-on-base (ℤ-to-code-base 𝟎) -- Use of the first computation rule for 𝕊¹-induction!
       II = ap loops (Idtofun-retraction code-on-base 𝟎)

\end{code}

We could show that encode x (decode x c) = c, but we don't.
After all, we only wanted to show that (base ≡ base) is a set.

\begin{code}

    open import UF-Retracts

    Ω𝕊¹-is-set : is-set (base ≡ base)
    Ω𝕊¹-is-set = subtypes-of-sets-are-sets (encode base)
                  (sections-are-lc (encode base)
                   ((decode base) , (decode-encode base)))
                   (transport is-set (code-on-base ⁻¹) ℤ-is-set)

\end{code}

\begin{code}

  module 𝕊¹-induction'
          (A : 𝕊¹ → 𝓥 ̇ )
          (a : A base)
          (l : transport A loop a ≡ a)
          (fe : funext 𝓤₀ 𝓤)
          (ua : is-univalent 𝓤₀)
         where

   open 𝕊¹-induction A a l

   𝕊¹-induction-on-loop' : transport (λ - → transport A loop - ≡ -)
                            𝕊¹-induction-on-base (apd 𝕊¹-induction loop)
                         ≡ l
   𝕊¹-induction-on-loop' = 𝕊¹-induction-on-loop (Ω𝕊¹-is-set ua fe)

   𝕊¹-induction-comp' : (𝕊¹-induction base , apd 𝕊¹-induction loop)
                      ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
   𝕊¹-induction-comp' = 𝕊¹-induction-comp (Ω𝕊¹-is-set ua fe)

\end{code}
