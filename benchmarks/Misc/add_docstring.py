from openai import OpenAI

base_url = 'https://llm.xmcp.ltd/'
api_key = 'sk-EQ-qfG8O_EbJFWPh0Ap9Xg'

client = OpenAI(api_key=api_key, base_url=base_url)

def add_docstring(code):
    system = 'You are an expert of Verus, the verification tool for Rust. You are given a Verus code, which corresponds to a text-level algorithm. You need to add the documentation for the code, at the beginning of the code. The documentation should be concise, which summarizes the functionality of the code in no more than two sentences. The docstring only NOT mention any information about verification. Output in the following format:\n/*[Your documentation Here]*/'

    user = code
    response = client.chat.completions.create(
        model='yunwu/hq-o4-mini-2025-04-16',
        messages=[
            {"role": "system", "content": system},
            {"role": "user", "content": user}
        ],
        max_tokens=100000,
    )

    return response.choices[0].message.content + '\n\n' + code

import os
for file in os.listdir('unverified'):
    if file.endswith('.rs'):
        with open(os.path.join('unverified', file), 'r') as f:
            code = f.read()
        docstring_code = add_docstring(code)
        with open(os.path.join('with_doc', file), 'w') as f:
            f.write(docstring_code)
    