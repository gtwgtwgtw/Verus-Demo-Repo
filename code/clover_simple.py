import re, sys, os, hashlib
from openai import AzureOpenAI


aoai_api_key="6mKL6q3U9UDbRZuJksQFcbW7EuJZ42qhxQWEHhLfQvvSUkOWDMMsJQQJ99BDACHYHv6XJ3w3AAAAACOGzX5o"
aoai_base_url="https://ai-chuyue997439ai270460324416.cognitiveservices.azure.com/"


client_azure = AzureOpenAI(
    azure_endpoint=aoai_base_url,
    api_key=aoai_api_key,
    api_version='2024-12-01-preview'
)

import os
def infer_llm(system: str, user: str, model: str, max_tokens=100000):
    key = hashlib.md5((system + user + model).encode()).hexdigest()
    #print(key, flush=True)
    cache_loc = os.path.join("cache", key)
    if os.path.exists(cache_loc):
        #print('hit')
        with open(cache_loc, "r") as f:
            return f.read()

    #print('miss')
    response = client_azure.chat.completions.create(
        messages=[
            {"role": "system", "content": system},
            {"role": "user", "content": user}
        ],
        model=model,
        max_completion_tokens=max_tokens
    ).choices[0].message.content

    with open(cache_loc, "w") as f:
        f.write(response)
    return response

pattern = re.compile(r'/\*.*?\*/', re.DOTALL)
def remove_comments_from_file(code: str):
    return pattern.sub('', code)

pid = 0
def add_docstring(code: str):
    system = 'You are an expert of Verus, the verification tool for Rust. You are given a Verus code, which corresponds to a text-level algorithm. You need to add the documentation for the code, at the beginning of the code. The documentation should be concise, which summarizes the functionality of the code in no more than two sentences. The docstring only NOT mention any information about verification. Output in the following format:\n/*[Your documentation Here]*/'

    global pid
    pid += 1
    user = code + f'\n\n/*{pid}*/'
    docstring = infer_llm(system, user, 'o4-mini')
    return docstring[:docstring.find('*/')+2]

def nl_equiv(doc1: str, doc2: str):
    system = f'[CURR TIME: {pid}]\n\nYou are an expert of natural language understanding. You are given two docstrings, named as `require` and `result`. You need to check if the docstring `result` has implemented the idea of the docstring `require`. Output in the following format: [YES or NO]\n[Reasons Here]'

    user = f'[Docstring `require`]\n{doc1}\n\n[Docstring `result`]\n{doc2}'
    response = infer_llm(system, user, 'o4-mini')
    #print(response)
    yes = response.startswith(('YES', '[YES'))
    return yes

def run(file_path: str):
    with open(file_path, 'r') as file:
        code = file.read()

    # Remove comments
    pos = code.find('*/') + 2
    doc = code[:pos]
    code = code[pos:]
    code = remove_comments_from_file(code)
    code = code.strip()
    #print(doc)
    #print('=' * 50)
    ans = 0
    for i in range(5):
        doc2 = add_docstring(code)
        #print(doc2)
        if nl_equiv(doc, doc2):
            ans += 1
        else:
            ans -= 1

    if ans > 0:
        print('Meets the Requirement')
    else:
        print('Does not Meet the Requirement')

if __name__ == "__main__":
    name = sys.argv[1]
    run(f'../result/final-result-{name}.rs')
