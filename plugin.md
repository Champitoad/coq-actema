# Actema comme plugin pour Coq

- plugin écrit en OCaml avec l'API de Coq prévue pour

- langage intermédiaire `Actema.proof` pour les preuves partielles d'Actema, aka
  le type de l'arbre de tactiques/actions + toutes les infos nécessaires à la
  compilation (typiquement la trace pour les DnD). Pas besoin d'une syntaxe
  élaborée, un dump de l'arbre en JSON est suffisant

- langage intermédiaire `Actema.state` pour le proof state d'Actema, là encore
  dumpable en JSON

- compilation `import_proof : Actema.proof -> unit tactic` par le plugin
  (possiblement en passant par une lib Coq/Ltac/MetaCoq)

- compilation `export_state : Proofview.proofview -> Actema.state` par le plugin

- le plugin expose 2 variantes de la même tactique : `actema` et `actema!`

- `{invokeID}` est un identifiant qui caractérise uniquement le proof state au
  lieu d'invocation de la tactique

- invocation de la tactique `actema` :

  * si `{invokeID}.actema` existe déjà, on se contente de recompiler l'objet de
  preuve Actema qu'il contient (mode interactif ou compilation);

  * sinon :

    + en mode **interactif**, on lance un serveur local et l'interface, et on
    connecte les deux (le serveur peut aussi servir l'interface ?). Le serveur
    envoie le proof state de Coq à Actema avec `export_state`, puis
    l'utilisateur fait son bout de preuve dans Actema. Bouton `Done` dans
    l'interface : ferme la fenêtre, envoie l'objet de preuve en JSON au serveur,
    puis le serveur le compile avec `import_proof` et l'écrit dans
    `{invokeID}.actema`

    + en mode **compilation**, on ne fait rien (`idtac`)

- `actema!` pareil qu'`actema` en mode compilation, force l'interface en mode
  interactif

- (?) argument supplémentaire `actionName : string` pour les deux tactiques
  permettant de nommer une preuve partielle Actema, afin de la sauvegarder (e.g.
  dans `{invokeID}-{actionName}.actema`) pour la réutiliser plus tard

Pros :

- S'intègre facilement dans un (environnement de) développement existant
- Accès direct aux termes déjà parsés
- Plus portable : moins de travail pour ajouter un plugin à un assistant de
preuve existant, uniquement besoin de compiler vers la logique sous-jacente