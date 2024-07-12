
- présentation actema
  -> exemples simples
  -> exemple des permutations sur les listes polymorphes (réutilisé dans les autres sections).
  
- langage actema (représentation des termes dans le prover)
  -> binders locally nameless
  
- pretty printer 
  -> 

- unification (+search)
  -> cadre particulier : le 'scope' des variables n'est pas connu avant l'unif
     contraster ça avec les néerlandais : ils utilisent directement l'unificateur de Coq,
     mais du coup l'ordre des règles est choisi avant l'unif ce qui fait que certains cas 
     ne sont pas traités
  -> parler aussi des propriétés théoriques (unicité de la solution etc.)
  -> bench l'optimisation de 'pré-unification' (liée au search)

- drag and drop certifiants (ltac2)
  -> sémantique big step avec certificat
  -> comparer approches certifiées et certifiante
