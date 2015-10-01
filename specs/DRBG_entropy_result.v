Require Import Coqlib.
Require Import List. Import ListNotations.

Inductive entropy_result :=
| entropy_error: entropy_result
| entropy_success: list Z -> entropy_result.