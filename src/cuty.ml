module M = Engine.Fo
module L = Engine.Location
module P = Engine.Parser
module X = Engine.Lexer
module G = Engine.Proof
module Y = Engine.Io

(** This module drives the web application. *)

(** [start_with goal] launches a worker that will interpret user
    actions to transform the state of the proof engine and to
    adjust the user interface accordingly.

    The system is initialized with [goal].

*)
let start_with goal =
  Lwt.async (
    fun () ->
      let enter_loop_event proof_state =
	let proof_state = ref proof_state in
	UI.next_user_action (fun action ->
	  try%lwt
	    let current_goal = ProofEngine.current_goal !proof_state in
	    let tactic = ProofEngineUI.tactic_of_user_action current_goal action  in
	    let dgoals = ProofEngine.apply !proof_state tactic in
	    let proof_state' = ProofEngine.change !proof_state dgoals in
	    UI.interpret dgoals >> (
	      proof_state := proof_state';
	      if ProofEngine.qed !proof_state then UI.qed () else Lwt.return ()
	    )
	  with ProofEngine.TacticFailed ->
	    Lwt.return (UI.notify "You cannot do that.")
	)
      in
      UI.interpret (Goals.push_goal goal) >>
      enter_loop_event (ProofEngine.start_proof_for goal)
  )

(** Install the interaction reactor into the DOM. *)
let main =
  Dom_html.window##.onload := Dom_html.handler (fun _ ->
    Random.self_init ();
    UI.init ();
    start_with Formula.(Goal.(make_goal [
      mk_atom "A";
      mk_conj [Atom "A"; Atom "B"]
    ] (mk_conj [Atom "A"; Atom "A"])));
    Js._false
  )
