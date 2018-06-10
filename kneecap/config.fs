(*
   Copyright 2015 Nik Sultana

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module config

Microsoft.Z3.Global.SetParameter("smtlib2_compliant", "true")

(*This affects some parts of the infrastructure. By knowing what the solver
  generates, we know whether we need to transform its output further to
  conform to protocol specs.*)
let solver_is_big_endian = true

(*Generator of distinct values, used to generate fresh names*)
let _next_fresh = ref 0
let get_fresh () =
  let cur_next = !_next_fresh
  _next_fresh := cur_next + 1
  cur_next.ToString()
