# UI 

- New entry in the radial menu : "search lemmas".
  This will look for all lemmas that can interact with the selected subterm
  and show each possible interaction (in a dropdown list or so).
- An interaction can be shown as a lemma + a selected subterm of the lemma. 
  A lemma can interact with the selected subterm in possibly several ways, e.g.
    my_lemma : A = B /\ A = C
  can interact with 
    ... [A] ...
  in two different ways.

- The user can then click on the lemma they want and it will interact.
  This will generate a link action where one of the ipaths points to (a subterm of) the lemma.

# Links

- Allow specifying an ipath into a lemma.
  Concretely : extend [item] to have an additionnal constructor. 
    item += `L of string * form
  where the string is the (unique) lemma name.

- Handle the execution of link actions where one of the paths is into a lemma 
  (should be very similar to the case of a hypothesis).

- Add a function to search for all links between a lemma and a conclusion/hypothesis subterm. 

# Actions

- When we generate all actions for a given selection, ([action], line 3133 of proof.ml) :
  include all linkactions between a lemma and the selected subterm.
  NO => only search for links in lemmas when the user wants to.