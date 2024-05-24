# Improve lemma search performance

- most time is probably spent on unification (check ?).
- add a basic unification test, faster but which rejects less programs
  (e.g. without dealing with unification variables) to be performed before real unification.

# Fix lemma order in the UI list

- have a deterministic order (e.g. sort alphabetically on lemma name).
- add a priority system. e.g. :
  - most recent lemmas first.
  - compute a matching degree, which could be the size of the subterm of the lemma that matches 
    the current selection (better measure than size of the permutation).

# Topics for the report 

- Talk about the pretty-printer (it's a GADT lol).
- Talk about the lemma search "fast" unification.