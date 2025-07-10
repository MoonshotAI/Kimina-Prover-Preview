from openai import OpenAI
from utils import extract_proof_from_text

SYSTEM = "You are an expert programmer and mathematician who helps formalizing mathematical problems in Lean 4."


STATEMENT_WITH_LEMMA = """import Mathlib


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
    (5^E) % 10000 = 3125 := by sorry"""


def main():
    API_URL = "http://localhost:8090/v1"
    KEY = "EMPTY"
    MODEL = "AI-MO/Kimina-Prover-Distill-1.7B"

    client = OpenAI(
        base_url=API_URL,
        api_key=KEY,
    )

    prompt = "Think about and solve the following problems step by step in Lean 4."
    prompt += "\n\n"
    prompt += STATEMENT_WITH_LEMMA

    messages = [
        {"role": "system", "content": SYSTEM},
        {"role": "user", "content": prompt},
    ]

    response = client.chat.completions.create(
        model=MODEL,
        messages=messages,
        temperature=0.1,
        max_tokens=8096,
        n=1,
    )

    text = response.choices[0].message.content
    formal_proof = extract_proof_from_text(text)
    print("Formal Proof:\n\n")
    print(formal_proof)


if __name__ == "__main__":
    main()
