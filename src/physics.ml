(* Ultra naive physic world. *)

let world_friction = 0.5
let reactivity = 0.5
let absorption = 0.3

type bbox = {
  id : Id.t;
  x : float;
  y : float;
  w : float;
  h : float;
  dx : float;
  dy : float;
}

type t = {
  width    : float;
  height   : float;
  boxes    : bbox list;
  friction : float
}

type dt = bbox list

let empty width height = {
  boxes = [];
  friction = world_friction;
  width;
  height;
}

let epsilon f = if f < 0.01 then 0. else f

let rec intersect a b =
  a.id <> b.id
  && (abs_float(a.x -. b.x) *. 2. <= (a.w +. b.w))
  && (abs_float(a.y -. b.y) *. 2. <= (a.h +. b.h))

let collide boxes box =
  List.find (intersect box) boxes

let update_box boxes box =
  List.map (fun box' -> if box.id = box'.id then box else box') boxes

let rec move friction boxes box =
  let box' =
    { box with
      x = box.x +. box.dx;
      y = box.y +. box.dy;
      dx = epsilon (box.dx *. friction);
      dy = epsilon (box.dy *. friction)
    }
  in
  try
    let box'' = collide boxes box' in
    let box'' = { box'' with dx = absorption *. box.dx; dy = absorption *. box.dy } in
    let boxes = update_box boxes box'' in
    let box'  = { box' with dx = -. absorption *. box.dx; dy = -. absorption *. box.dy } in
    update_box boxes box'
  with Not_found ->
    update_box boxes box'

let next world =
  let boxes' = List.fold_left (move world.friction) world.boxes world.boxes in
  let dboxes = List.(
    combine world.boxes boxes'
    |> filter (fun (b1, b2) -> b1 <> b2)
    |> split
    |> snd
  ) in
  { world with boxes = boxes' }, dboxes

let new_box world id width height =
  let rec find_place () =
    let box = {
      id;
      x = Random.float world.width;
      y = Random.float world.height;
      w = width;
      h = height;
      dx = Random.float 10.;
      dy = Random.float 10.;
    }
    in
    try ignore (collide world.boxes box); find_place () with _ -> box
  in
  let box = find_place () in
  { world with boxes = box :: world.boxes }, box

let remove_box world id =
  { world with boxes = List.filter (fun box -> box.id <> id) world.boxes }

let change_box_attraction world id x y = try
  let box = List.find (fun box -> box.id = id) world.boxes in
  let dx = x -. box.x and dy = y -. box.y in
  (* let r = reactivity *. (dx *. dx +. dy *. dy) in *)
  let dx = reactivity *. dx and dy = reactivity *. dy in
  (* Firebug.console##log_3 (Js.string "pos: ", box.x, box.y); *)
  (* Firebug.console##log_3 (Js.string "npos: ", x, y); *)
  (* Firebug.console##log_3 (Js.string "dir: ", dx, dy); *)
  let boxes = List.map (fun box ->
    if box.id = id then { box with dx; dy } else box
  ) world.boxes
  in
  { world with boxes }
with _ -> world
