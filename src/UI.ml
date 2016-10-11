open Id
open Lwt
open Goal
open Goals
open Formula
open Physics
module T = Tyxml_js.Html5

type user_action =
  | Use of Id.t
  | Transform of Id.t

let string_of_user_action = function
  | Use id -> "Use " ^ Id.string_of_id id
  | Transform id -> "Transform " ^ Id.string_of_id id

let (actions : user_action Lwt_stream.t), push_user_action =
  Lwt_stream.create ()

let next_user_action f =
  Lwt_stream.iter_s f actions

let empty_world () = ref (Physics.empty 512. 256.)

let empty_nodes () = Hashtbl.create 13

let stack = ref []

let world () = ! (fst (List.hd !stack))
let update_world world' = (fst (List.hd !stack)) := world'
let nodes () = snd (List.hd !stack)

let switch_world_visibility flag =
  if !stack <> [] then
    let state = if flag then "visible" else "hidden" in
    Hashtbl.iter (fun _ node ->
      node##style##visibility <- Js.string state
    ) (nodes ())

let push_world () =
  switch_world_visibility false;
  stack := (empty_world (), empty_nodes ()) :: !stack

let pop_world () =
  switch_world_visibility false;
  stack := List.tl !stack;
  switch_world_visibility true

let qed () =
  ignore (CutyBackEnd.new_node (T.(div ~a:[a_class ["qed"]] [pcdata "QED"])) ignore);
  return ()

let move_box box =
  let floor x = int_of_float (floor x) in
  let node = Hashtbl.find (nodes ()) box.id in
  node##style##top <- Js.string (string_of_int (floor box.y) ^ "px");
  node##style##left <- Js.string (string_of_int (floor box.x) ^ "px")

let refresh () =
  if !stack <> [] then (
    let world', dworld = Physics.next (world ()) in
    update_world world';
    List.iter move_box dworld
  )

let init () =
  ignore (Dom_html.window##setInterval (Js.wrap_callback refresh, 100.))

let get_element_dimension (e : Dom_html.element Js.t) =
  let b = e##getBoundingClientRect () in
  let width = Js.Optdef.get (b##width) (fun () -> float_of_int e##offsetWidth) in
  let height = Js.Optdef.get (b##height) (fun () -> float_of_int e##offsetHeight) in
  (width, height)

let create_node_in_world id node =
  let (width, height) = get_element_dimension node in
  Hashtbl.add (nodes ()) id node;
  let world', box = Physics.new_box (world ()) id width height in
  update_world world';
  move_box box

let rec separated e = function
  | [] -> []
  | [x] -> [x]
  | x :: l -> x :: e () :: separated e l

let wedge () = T.(div ~a:[a_class ["formula"]] [pcdata "∧"])

let activate l element =
  ignore (CutyBackEnd.new_node element (fun event ->
    () (* Firebug.console##log_2 (event, Js.string (string_of_location l)) *)
  ));
  element

let element_of_formula color f = T.(
  let a = [a_class ["formula"]; a_style ("color:" ^ color ^ ";")] in
  Formula.map f
    (* Atom *) (fun l s -> activate l (div ~a [ pcdata s ]))
    (* Conj *) (fun l e -> activate l (div ~a (separated wedge e)))
)

let element_of_formula_box color t =
  let box = T.(div ~a:[a_class ["formula_box"]] [element_of_formula color t]) in
  ignore (CutyBackEnd.new_node box (fun (kind, positions) ->
  (*    List.iter (fun (x, y) -> Firebug.console##log_2 (x, y)) positions *)
  (* Firebug.console##log (positions) *)
    ()
  ));
  box

let push_user_event nodeid (kind, positions) =
  return CutyBackEnd.(match kind with
    | Tap -> push_user_action (Some (Use nodeid))
    | DoubleTap -> push_user_action (Some (Transform nodeid))
    | Pan -> ()
    | PanStart -> ()
    | PanMove (x, y) ->
      let x = float_of_int x and y = float_of_int y in
      update_world (Physics.change_box_attraction (world ()) nodeid x y)
    | PanEnd -> ()
  )

let push_formula color { identifier = id; term } =
  let elem = element_of_formula_box color term in
  let node = CutyBackEnd.new_node elem (push_user_event id) in
  create_node_in_world id node;
  Lwt.return ()

let push_hypothesis =
  push_formula "#0000FF"

let push_conclusion =
  push_formula "#FF0000"

let clear_hypothesis id =
  let node = Hashtbl.find (nodes ()) id in
  node##style##visibility <- Js.string "hidden";
  Hashtbl.remove (nodes ()) id;
  update_world (Physics.remove_box (world ()) id);
  Lwt.return ()

let push_goal g =
  push_world ();
  Lwt_list.iter_s push_hypothesis g.hypothesis
  >> push_conclusion g.conclusion

let pop_goal g =
  pop_world ();
  return ()

let rec interpret = function
  | OnCurrent (ClearHypothesis id) -> clear_hypothesis id
  | OnCurrent (PushHypothesis f) -> push_hypothesis f
  | PushGoal g -> push_goal g
  | PopGoal g -> pop_goal g
  | Identity -> return ()
  | Compose dgoals -> Lwt_list.iter_s interpret dgoals

let notify msg =
  CutyBackEnd.notify msg
