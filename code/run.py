import os, subprocess

for file in os.listdir('../test'):
    if file.endswith('.rs'):
        tfile = file[:-3]
        print(tfile, flush=True)
        try:
            subprocess.run(
                f'python3 spec_main.py {tfile}',
                shell=True,
                text=True,
                timeout=1800
            )
        except:
            print(f'Error at {file}', flush=True)
        #break