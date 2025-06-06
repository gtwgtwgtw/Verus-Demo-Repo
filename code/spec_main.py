from openai import AzureOpenAI
import sys

aoai_api_key="6mKL6q3U9UDbRZuJksQFcbW7EuJZ42qhxQWEHhLfQvvSUkOWDMMsJQQJ99BDACHYHv6XJ3w3AAAAACOGzX5o"
aoai_base_url="https://ai-chuyue997439ai270460324416.cognitiveservices.azure.com/"


client_azure = AzureOpenAI(
    azure_endpoint=aoai_base_url,
    api_key=aoai_api_key,
    api_version='2024-12-01-preview'
)

#for model in client_azure.models.list():
#    print(model.id, flush=True)
#sys.exit(1)

from hashlib import md5
import os

os.system('rm cache/*')

def infer_llm(system: str, user: str, model: str, max_tokens=16384):
    key = md5((system + user + model).encode()).hexdigest()
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
        seed=42,
        model=model,
        max_completion_tokens=max_tokens
    ).choices[0].message.content

    with open(cache_loc, "w") as f:
        f.write(response)
    return response


require_keyword = '[Require Synthesized]'
len_require_keyword = len(require_keyword)
ensures_keyword = '[Ensures Synthesized]'
len_ensures_keyword = len(ensures_keyword)
def parse_result(response: str):
    pos = response.find(require_keyword)
    req = ''
    if pos != -1:
        pos += len_require_keyword
        end_pos = response.find('[End Require]', pos)
        if end_pos != -1:
            req = response[pos:end_pos]
    
    pos = response.find(ensures_keyword)
    ens = ''
    if pos != -1:
        pos += len_ensures_keyword
        end_pos = response.find('[End Ensures]', pos)
        if end_pos != -1:
            ens = response[pos:end_pos]

    return req, ens


SYSTEM = (
"""
You are an expert at Verus, a formal verification tool for Rust. You will be given a Verus code, with a docstring at the beginning that showing the functionality of the code.

Your goal is to fill in requires and ensures clauses in a given verus program, and make sure that the requires and ensures align the docstring at the beginning. 

The to-be-filled requires (or ensures) part have been tagged with // [Add Requires (or Ensures) Clauses Here] in the code.

Output in the following format:
[Require Synthesized]
<requires clause 1>,
<requires clause 2>,
...
<requires clause n>
[End Require]
[Ensures Synthesized]
<ensures clause 1>,
<ensures clause 2>,
...
<ensures clause n>
[End Ensures]


After you have synthesized these clauses, I will fill these clauses into the code as.
```verus
requires
<requires clauses you synthesized here>
ensures
<ensures clauses you synthesized here>
```

Thus, NEVER synthesize the clauses beginnin with `requires` and `ensures`.

Important notes:
- Think over to guarantee the correctness of the code, and make sure that the requires and ensures clauses are correct.
- Some functions have been tagged with // [Trusted], which means that you can trust the code in this part and do not need to modify it.
"""
)

SYSTEM_REPAIR = (
"""
You are an expert at Verus, a formal verification tool for Rust. You will be given:
(1) a Verus code, with a docstring at the beginning that showing the functionality of the code. 
(2) The error message from the Verus compiler, which indicates the verification failure.
(3) Previous Failure Code generated by LLM.


Your goal is to repair the code so that:
(1) The code can pass the verification.
(2) The code meets the functionality described in the docstring.
(3) Also generate loop invariants if necessary.

Output in the following format:
```verus
<your repaired code here>
```

Important notes:
- Think over to guarantee the correctness of the code.
- Some functions have been tagged with // [Trusted], which means that you can trust the code in this part and do not need to modify it.
"""
)

SYSTEM_GENERATE = (
"""
You are an expert at Verus, a formal verification tool for Rust. Your task is to generate a Verus code from a given docstring showing the functionality of the code should be.

Please make sure:
(1) The code can pass the verification.
(2) The code meets the functionality described in the docstring.
(3) Also generate loop invariants if necessary.
(4) Write requires and ensures clauses for the code, and make sure that the requires and ensures align the docstring at the beginning.

Output in the following format:
```verus
use vstd::prelude::*;

verus!{
<your generated code here>
}

fn main() {}
```

Important notes:
- Think over to guarantee the correctness of the code.
"""
)

import subprocess

def wrap(text, header):
    return f'{header}\n{text.strip()}'

def add_doc(docstring, code):
    code = code.strip()
    if code.startswith(docstring):
        return code
    return docstring + '\n' + code

def print_failures(failures):
    ans = '### Previous Failures: \n\n'
    for code, log in failures:
        ans += ('### Generated Code:') + '\n\n'
        ans += (code) + '\n\n'
        ans += ('### Error Message:') + '\n\n'
        ans += (log) + '\n\n'
    return ans

def trunc(text, length):
    if len(text) > length-3:
        return text[:length-3] + '...'
    return text

def run(file_path: str):
    with open(file_path, 'r') as f:
        code = f.read()
    
    docstring = code[:code.find('*/')+2]
    with open('../tmp/code.rs', 'w') as f:
        f.write(docstring)
    code = code[code.find('*/')+2:]
    if len(sys.argv) >= 3 and sys.argv[2] == '--generate':
        print(f'✍️ LLM is writing codes', flush=True)
        response = infer_llm(SYSTEM_GENERATE, docstring, "o1", 100000)
        code = response[response.rfind('```verus')+len('```verus'):response.rfind('```')].strip()
        print(f'💡 LLM code writing is done', flush=True)

    failures = []

    final_path = f'../result/final-result-{sys.argv[1]}.rs'

    with open(final_path, 'w') as f:
        f.write(docstring + '\n' + code)
    with open('../tmp/code.rs', 'w') as f:
        f.write(docstring + '\n' + code)

    for i in range(15):
        if '[Add' not in code:
            print(f'💻 Checking Verus Validity', flush=True)
        subprocess.run(
            f'verus {final_path} > ../tmp/verus.log 2>&1 --verbose',
            shell=True
        )
        with open('../tmp/verus.log', 'r') as f:
            log = f.read()
        with open(final_path, 'r') as f:
            code = f.read()
        if 'error:' in log:
            code = '// [FAILED] ' + code
        if '// [FAILED]' not in code and not '[Add' in code:
            print(f'😊 Code is Verified!', flush=True)
            break

        if '// [FAILED]' in code:
            code = code[code.rfind('// [FAILED]')+len('// [FAILED]'):].strip()
            print(f'❌ Code is NOT Verified! The verus compiler reports:\n{trunc(log, 1024)}', flush=True)
            failures += [(code, log)]
        
        if code.find('// [Add Requires Clauses Here]') != -1 or code.find('// [Add Ensures Clauses Here]') != -1:
            print('🤔 Requires and Ensures Missing, filling it...', flush=True)
            response = infer_llm(SYSTEM, add_doc(docstring, code), "o1", 100000)
            req, ens = parse_result(response)
            code = code.replace('// [Add Requires Clauses Here]', 
                            wrap(req, 'requires'))
            code = code.replace('// [Add Ensures Clauses Here]', 
                            wrap(ens, 'ensures'))
            print('💡 Requires and Ensures filled', flush=True)
        else:
            print('⚙️ Repair the code based on the error message', flush=True)
            user = add_doc(docstring, code) + 'Error Message:\n\n' + log + '\n\n' + print_failures(failures[:-1])
            response = infer_llm(SYSTEM_REPAIR, user, "o1", 100000)
            code = response[response.rfind('```verus')+len('```verus'):response.rfind('```')].strip()
            print('💡 Repair is done, try to refine the proof', flush=True)

        doc_code = add_doc(docstring, code)
        #print(doc_code)
        with open(f'../result/intermediate.rs', 'w') as f:
            f.write(doc_code)
        with open(final_path, 'w') as f:
            f.write(doc_code)
        with open('../tmp/code.rs', 'w') as f:
            f.write(doc_code)

        print('🤔 Proof Refining', flush=True)
        subprocess.run(
            f'python3 main.py --input ../result/intermediate.rs',
            shell=True,
            text=True
        )
        print('💡 Proof Refined', flush=True)

        with open('output.rs', 'r') as f:
            code = f.read()
        code = add_doc(docstring, code)

        with open(final_path, 'w') as f:
            f.write(code)
        with open('../tmp/code.rs', 'w') as f:
            f.write(code)

         
if __name__ == '__main__':
    run(f'../test/{sys.argv[1]}.rs')