import json

# Make sure we have installed kimina-lean-server, or add the path of kimina-lean-server
from client import Lean4Client
from openai import OpenAI
from utils import create_tool_message, extract_proof_from_text, parse_client_response


def verify_proof_with_lean_feedback(
    formal_proof: str, url="http://127.0.0.1:12332"
) -> dict:
    """
    Verify the formal proof using Lean 4 and return the feedback.
    Args:
        formal_proof: The formal proof string to verify.
        url: default URL for the kimina-lean-server.
    Returns:
        A dict containing the proof ID, formal proof, Lean feedback, and validation results.
        proof_id: A unique identifier for the proof.
        proof: The formal proof string.
        lean_feedback: The feedback from Lean 4 in JSON string format.
        has_error: A boolean indicating if there are any errors in the proof.
        is_valid_no_sorry: A boolean indicating if the proof is valid allowing "sorry" in the proof.
        is_valid_with_sorry: A boolean indicating if the proof is valid without allowing "sorry"
    """
    proof_id = "0"

    lean_client = Lean4Client(base_url=url)
    code = {
        "custom_id": proof_id,
        "proof": formal_proof,
    }

    response = lean_client.verify([code], timeout=60, infotree_type="original")
    result = response["results"][0]

    parsed_result = parse_client_response(result)

    return {
        "proof_id": proof_id,
        "proof": formal_proof,
        "lean_feedback": json.dumps(result),
        "has_error": parsed_result["has_error"],
        "is_valid_no_sorry": parsed_result["is_valid_no_sorry"],
        "is_valid_with_sorry": parsed_result["is_valid_with_sorry"],
    }


SYSTEM = "You are an expert programmer and mathematician who helps formalizing mathematical problems in Lean 4."


STATEMENT_WITH_LEMMA = """import Mathlib

theorem five_pow_last_digits : ∀ (E : ℕ), 4 ≤ E → E ≡ 1 [MOD 4] → (5 ^ E) % 10000 = 3125 := by sorry"""


def main():
    API_URL = "http://localhost:8090/v1"
    KEY = "EMPTY"
    MODEL = "AI-MO/Kimina-Prover-Distill-1.7B"
    MAX_TOKENS = 16000
    OUTPUT_FILE = "error_fix_output.json"

    client = OpenAI(
        base_url=API_URL,
        api_key=KEY,
    )

    prompt = "Think about and solve the following problems step by step in Lean 4."
    prompt += "\n\n"
    prompt += STATEMENT_WITH_LEMMA

    # create query for the first turn generation
    messages = [
        {"role": "system", "content": SYSTEM},
        {"role": "user", "content": prompt},
    ]

    print("Generating the first turn of the proof...")
    response = client.chat.completions.create(
        model=MODEL,
        messages=messages,
        temperature=0.8,
        presence_penalty=0.2,
        max_tokens=MAX_TOKENS,
        n=1,
    )
    text = response.choices[0].message.content
    messages.append(
        {
            "role": "assistant",
            "content": text,
        }
    )

    # analyse the first turn output
    print("Analyzing the first turn output using kimina-lean-server...")
    formal_proof = extract_proof_from_text(text)
    first_turn_result = verify_proof_with_lean_feedback(formal_proof)
    proof_is_valid = first_turn_result["is_valid_no_sorry"]
    if proof_is_valid:
        print("Proof of first turn is valid !")
        with open(OUTPUT_FILE, "w") as f:
            json.dump(messages, f)
        return
    else:
        print("Proof of first turn is not valid :( Apply error fixing.")

    # if first turn proof is not valid, we need to apply error fixing
    lean_feedback = json.loads(first_turn_result["lean_feedback"])
    formatted_output = create_tool_message(
        formal_code=formal_proof,
        lean_feedback=lean_feedback,
    )
    messages.append(
        {
            "role": "user",
            "content": formatted_output,
        }
    )
    print("Generating the error fix turn of the proof...")
    response = client.chat.completions.create(
        model=MODEL,
        messages=messages,
        temperature=0.8,
        max_tokens=MAX_TOKENS,
        n=1,
    )
    text = response.choices[0].message.content
    messages.append(
        {
            "role": "assistant",
            "content": text,
        }
    )
    print("Analyzing the error fix turn output using kimina-lean-server...")
    formal_proof = extract_proof_from_text(text)
    error_fix_turn_result = verify_proof_with_lean_feedback(formal_proof)
    proof_is_valid = error_fix_turn_result["is_valid_no_sorry"]
    if proof_is_valid:
        print("Proof of error fix turn is valid !")
    else:
        print("Proof of error fix turn is still not sucessful :( Please try again.")

    with open(OUTPUT_FILE, "w") as f:
        json.dump(messages, f)
    print("Output saved to error_fix_output.json")


if __name__ == "__main__":
    main()
