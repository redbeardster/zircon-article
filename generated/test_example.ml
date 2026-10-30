(* Driver for Isabelle-extracted code.
   File Zircon.ml defines nested module Zircon, hence Zircon.Zircon. *)

let () =
  let ok_main = Zircon.Zircon.example_exec_ok in
  let ok_empty = Zircon.Zircon.example_empty_exec_ok in
  if ok_main && ok_empty then (
    print_endline "PASS: example_exec_ok = true";
    print_endline "PASS: example_empty_exec_ok = true";
    exit 0
  ) else (
    if not ok_main then print_endline "FAIL: example_exec_ok = false";
    if not ok_empty then print_endline "FAIL: example_empty_exec_ok = false";
    exit 1
  )
