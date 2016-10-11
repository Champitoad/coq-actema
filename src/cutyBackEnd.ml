open Js.Unsafe

let board () =
  Dom_html.getElementById "playground"

type kind =
  | Pan
  | Tap
  | Press
  | Pinch
  | Rotate
  | DoubleTap
  | PanStart
  | PanEnd
  | PanMove of int * int
  | Nothing

let kind_of_event event =
  match Js.to_string (event##_type) with
    | "pan" -> Pan
    | "doubletap" -> DoubleTap
    | "panmove" -> PanMove (event##center##x, event##center##y)
    | "panstart" -> PanStart
    | "panend" -> PanEnd
    | "tap" -> Tap
    | _ -> Nothing

open Js

class type tevent = object
  method pointers : pointerList t readonly_prop
end

and pointerList = object
  method length : int readonly_prop
  method item : int -> Dom_html.touch t optdef meth
end

let touch_event_positions (event : tevent Js.t) =
  let r = ref [] in
  for i = 0 to event##.pointers##.length - 1 do
    let item = event##.pointers##item (i) in
    Js.Optdef.iter item (fun item ->
      r := (item##.clientX, item##.clientY) :: !r
    )
  done;
  !r

let mouse_event_positions event =
  [(event##clientX, event##clientY)]

let positions event =
  if event##pointerType = Js.string "touch" then
    touch_event_positions (Obj.magic event)
  else if event##pointerType = Js.string "mouse" then
    mouse_event_positions event
  else
    []

let wrap callback event =
  callback (kind_of_event event, positions event)

let new_node doc (on_event : _ -> 'a) =
  let element = Tyxml_js.To_dom.of_element doc in
  let node = (element :> Dom.node Js.t) in
  ignore ((board ())##appendChild (node));
  ignore (fun_call (eval_string "backend_new_node") [|
    inject element;
    inject (Js.wrap_callback (wrap on_event))
  |]);
  element

let notify msg =
  ignore (fun_call (eval_string "backend_notify") [|
    inject (Js.string msg)
  |])
