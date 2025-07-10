import re


def split_proof_header(proof):
    proof = proof.strip()
    header_lines = []
    context_lines = []
    toggle = False
    proof_lines = proof.split("\n")
    index = 0
    for line in proof_lines:
        if line.startswith("import"):
            if toggle is False:
                toggle = True
            header_lines.append(line)
            index += 1
        else:
            if toggle is True:
                toggle = False
                break
    context_lines = proof_lines[index:]
    return "\n".join(header_lines).strip(), "\n".join(context_lines)


def position_greater_or_equal(pos1, pos2):
    """
    Check if the position pos1 is greater than pos2.
    """
    if not isinstance(pos1, dict) or not isinstance(pos2, dict):
        return False

    line1 = pos1["line"]
    col1 = pos1["column"]
    line2 = pos2["line"]
    col2 = pos2["column"]

    if line1 > line2:
        return True
    elif line1 == line2 and col1 >= col2:
        return True
    else:
        return False


def position_distance(pos1, pos2):
    """
    Calculate the distance between two positions.
    """
    if not isinstance(pos1, dict) or not isinstance(pos2, dict):
        return float("inf")

    line1 = pos1["line"]
    col1 = pos1["column"]
    line2 = pos2["line"]
    col2 = pos2["column"]

    return 10 * abs(line1 - line2) + abs(col1 - col2)


def get_error_node(infotree, startPos, endPos):
    """find a tactic state containing the error message,
    which has the shortest length"""
    stack = list(infotree)  # initialize stack with top-level nodes
    tree_candidates = []
    while stack:
        tree = stack.pop()
        try:
            stxRange = tree["node"]["stx"]["range"]
            if not isinstance(stxRange, dict):
                continue
        except (KeyError, TypeError):
            continue

        start_is_in_range = position_greater_or_equal(stxRange.get("start"), startPos)
        end_is_in_range = position_greater_or_equal(endPos, stxRange.get("finish"))

        if start_is_in_range and end_is_in_range:
            distance = position_distance(stxRange.get("start"), startPos)
            distance += position_distance(stxRange.get("finish"), endPos)
            tree_candidates.append(
                {
                    "node": tree,
                    "distance": distance,
                }
            )

        # Add children to stack if they exist
        children = tree.get("children", [])
        if isinstance(children, list):
            stack.extend(children)
    if not tree_candidates:
        return None
    closest_tree = min(
        tree_candidates,
        key=lambda x: x["distance"],
    )
    return closest_tree["node"]


def find_goals_state(message, feedback):
    """
    add tactic state to the message object if applicable
    """
    if "pos" not in message or "endPos" not in message:
        return None
    error_node = get_error_node(
        feedback.get("infotree", []), message["pos"], message["endPos"]
    )
    if error_node:
        error_node = error_node.get("node", {})
        goals_state = error_node.get("goalsBefore") or error_node.get("goalsAfter")
        return goals_state
    return None


def filter_error_messages(feedback):
    """Filter messages to keep only those with severity 'error'."""
    if not (feedback.get("response") and feedback["response"].get("messages")):
        return []

    error_messages = [
        msg
        for msg in feedback["response"]["messages"]
        if isinstance(msg, dict) and msg.get("severity") == "error"
    ]

    return error_messages[:3]


def create_tool_message(
    formal_code,
    lean_feedback,
):
    """Create a single task from a formal code and Lean feedback."""
    error_messages = filter_error_messages(lean_feedback)

    _, context = split_proof_header(formal_code)
    proof_lines = context.split("\n")
    response = lean_feedback.get("response")

    formatted_output = ""
    # find error with infotree
    for i, error in enumerate(error_messages, 1):

        pos = error.get("pos")
        error_msg = error.get("data", "Unknown error")
        # error_msg = re.sub(r'\s+', ' ', error_msg).strip()

        formatted_output += f"# Error {i}:\n"
        # formatted_output += f"Error message: \n{error_msg.strip()}\n\n"
        output_dict = {
            "error_message": error_msg.strip(),
            "goals_state": None,
            "code snippet": None,
        }
        if pos:
            line_num = pos.get("line", 1) - 1
            if "line" in pos:
                # only compute the goals state if the line number is valid
                goals_state = find_goals_state(error, response)
                if goals_state:
                    goals_message = "\n".join(goals_state)
                    # formatted_output += f"Goals state: \n{goals_message}\n\n"
                    output_dict["goals_state"] = goals_message

            start_line = max(0, line_num - 2)
            end_line = min(len(proof_lines), line_num + 3)

            # formatted_output += "Lean 4 code snippet with error:\n```lean4\n"
            snippet = "```lean4\n"
            for ln in range(start_line, end_line):
                proof_line = proof_lines[ln].replace("count_heartbeats in", "")
                snippet += (
                    f"{ln+1:03d}{' >' if ln == line_num else '  '}| {proof_line}\n"
                )
            output_dict["code snippet"] = snippet + "```"

        # add goals state to the output dict
        if output_dict["goals_state"]:
            formatted_output += (
                f"Goals state before error position: \n{output_dict['goals_state']}\n\n"
            )
        # add error message to the output dict
        formatted_output += f"Error message: \n{output_dict['error_message']}\n\n"
        # add code snippet to the output dict
        if output_dict["code snippet"]:
            formatted_output += (
                f"Lean 4 code snippet with error:\n{output_dict['code snippet']}\n"
            )

    if formatted_output == "":
        top_level_error = lean_feedback.get("error")
        if top_level_error and top_level_error.strip():
            formatted_output += "# System Error:\n"
            formatted_output += f"Error message: \n{top_level_error.strip()}\n\n"
    return formatted_output


def extract_proof_from_text(output: str) -> str:
    """
    Parse the proof from the model output for thinking models.
    Takes the last code inside ```lean4 and ``` that has the formal statement inside
    Args:
        output: The model output string.
    Returns:
        The parsed proof string.
    """
    lean4_codes = re.findall(r"```lean4\n(.*?)\n```", output, re.DOTALL)
    words = ["theorem", "by", ":=", "import"]

    for i in range(len(lean4_codes)):
        lean4_code = lean4_codes[-i - 1]
        if all(word in lean4_code for word in words):
            return lean4_code

    return "No proof found in the output."  # this will not pass verification


def has_error(
    feedback: dict, accept_sorry: bool = True, return_error_messages: bool = False
):
    """
    Checks if the Lean feedback contains an error.

    Args:
    - feedback: The Lean feedback as a dictionary.
    - accept_sorry: Whether to accept "sorry" statements as "not an error".
    By default, "sorry" statements are not considered errors.
    """

    if "error" in feedback:
        r = (True, [feedback["error"]]) if return_error_messages else True
        return r

    if "stderr" in feedback:
        r = (True, [feedback["stderr"]]) if return_error_messages else True
        return r

    has_error = False
    error_data_values = []
    sorry_data_values = []
    if "messages" in feedback:
        error_data_values = [
            message["data"]
            for message in feedback.get("messages", [])
            if message.get("severity") == "error"
        ]
        has_error = bool(error_data_values)

        if not accept_sorry:
            warning_data_values = [
                message["data"]
                for message in feedback.get("messages", [])
                if message.get("severity") == "warning"
            ]
            sorry_data_values = [
                warning_data
                for warning_data in warning_data_values
                if "declaration uses 'sorry'" in warning_data
            ]
            has_error = has_error or bool(sorry_data_values)

    if return_error_messages:
        return has_error, error_data_values + sorry_data_values
    else:
        return has_error


def parse_client_response(response: dict):
    """Parses the response from the Lean4Client.
    Reponse should be the output of autoformalizer.clients.lean4_client.Lean4Client.one_pass_verify

    Args:
        - response (dict): The response from the Lean4Client.

    Returns:
        - dict: A dictionary containing the following keys:
            - has_error: Whether the response contains an error.
            - is_valid_no_sorry: Whether the response is valid without "sorry" statements.
                this is used for proof verification.
            - is_valid_with_sorry: Whether the response is valid with "sorry.
                this is used for statement verification.
    """
    error_message = response.get("error", None)
    json_response = response.get("response", None)

    error = bool(error_message) or has_error(json_response)
    is_valid_no_sorry = (not bool(error_message)) and (
        not has_error(json_response, accept_sorry=False)
    )
    is_valid_with_sorry = (not bool(error_message)) and (
        not has_error(json_response, accept_sorry=True)
    )

    return {
        "has_error": error,
        "is_valid_no_sorry": is_valid_no_sorry,
        "is_valid_with_sorry": is_valid_with_sorry,
    }
