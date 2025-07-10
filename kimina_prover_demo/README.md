# Demo of Kimina-Prover

Kimina Prover is equiped with two new capacities: multi turn error fixing and lemma use. Here we provide two demo scripts to show how to use the model in these cases.

## Set up
Install requirements
```bash
pip install -r requirements.txt
```

Serve the Kimina Prover model. You can pick one from https://huggingface.co/collections/AI-MO/kimina-prover-686b72614760ed23038056c5

```bash
vllm serve --host 0.0.0.0 --port 8090 AI-MO/Kimina-Prover-Distill-1.7B
```

## Lemma use
When provided a lemma, the model with try its best to leverage the lemma to solve the problem. Here is an example of input for the model

```lean4
import Mathlib

lemma lemma_1 : ∀ (E : ℕ), 4 ≤ E → E ≡ 1 [MOD 4] → (5 ^ E) % 10000 = 3125 := by
  intro E hE1 hE2
  have h1 : E % 4 = 1 := hE2
  have h2 : E ≥ 4 := hE1
  have h3 : ∀ k : ℕ, 5 ^ (4 * k + 5) % 10000 = 3125 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h4 : 5 ^ (4 * (k + 1) + 5) = 5 ^ (4 * k + 5) * 5 ^ 4 := by ring_nf
      rw [h4]
      rw [Nat.mul_mod]
      rw [ih]
      all_goals
        norm_num
  have h4 : E % 4 = 1 := h1
  have h5 : ∃ k : ℕ, E = 4 * k + 1 := by
    refine' ⟨(E - 1) / 4, by omega⟩
  rcases h5 with ⟨k, hk⟩
  have h6 : k ≥ 1 := by
    omega
  have hk2 : E = 4 * (k - 1) + 5 := by
    omega
  rw [hk2]
  apply h3 (k - 1)


theorem number_theory_9df47017272f {E : ℕ} (hE : E = 123456789012345678901) :
    (5^E) % 10000 = 3125 := by sorry
```

To see the output, run
```bash
python lemma_use.py
```


## Error Fixing

When a proof fails, one can now provide a formatted error message as user message for the model to try to fix it.
Error message comes from lean infotree, and is formatted using `utils.create_tool_message`

```
# Error 1:
Goals state before error position: 
case succ
E : ℕ
h1 : 4 ≤ E
h2 : E ≡ 1 [MOD 4]
h3 : E % 4 = 1
h4 : E ≥ 4
h5 : 5 ^ E % 16 = 5
h9 : E ≥ 4
k : ℕ
ih : 5 ^ (4 + k) % 625 = 0
⊢ 5 ^ (4 + (k + 1)) % 625 = 0

Error message: 
omega could not prove the goal:
a possible counterexample may satisfy the constraints
  1 ≤ b - 625*c ≤ 624
  a ≥ 1
where
 a := ↑E / 4
 b := ↑5 ^ (4 + (k + 1))
 c := ↑(5 ^ (4 + (k + 1))) / 625
 ```

In order to run error fixing, you need to set up a lean server. Please refer to the `Install kimina-lean-server` section.

Once the server server is ready, you can run 
```bash
python error_fix.py
```

You can find the output messages at `error_fix_output.json`


# Install kimina-lean-server

```bash
git clone https://github.com/project-numina/kimina-lean-server
cd kimina-lean-server
```

## Install dependencies
```bash
pip install -e .
```

## Start lean server


### Install mathlib and repl

First, install elan — the Lean version manager: [reference](https://github.com/leanprover/elan).

After installing elan, make sure that `elan --version` works correctly.
(`lake --version` should also work after elan is properly installed.)


```bash
chmod +x setup.sh && ./setup.sh
```

### Start the server
```bash
python -m server
```

When see `Created N ['import Mathlib\nimport Aesop'] repls with response`, it means the startup is successful.

For more detailed installation instructions, please refer to [this](https://github.com/project-numina/kimina-lean-server)