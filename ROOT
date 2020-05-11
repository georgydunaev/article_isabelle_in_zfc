chapter AFP

(* There must be one session with the (short) name of the entry.
   This session generates the web document and HTML files.

   It is strongly encouraged to have precisely one session, but it
   if needed, further sessions are permitted.

   All sessions must be in group (AFP) - otherwise they are not
   run upon submission and by the later automatic regression tests.

   Every theory must be included in at least one of the sessions.
*)

(* Session name, add to AFP group, list base session: *)
session "Recursion-Addition" (AFP) = ZF +

(* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 600]

(* To suppress document generation of some theories: *)
(*
  theories [document = false]
    This_Theory
    That_Theory
*)

(* The top-level theories of the submission: *)
  theories
    recursion

(* Dependencies on document source files: *)

  document_files
(*    "root.bib" *)
    "root.tex"

