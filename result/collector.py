import os

ans = []
for file in os.listdir('.'):
    if file.startswith('final-result-'):
        content = open(file, 'r').read()
        if content.find('[FAILED]') != -1:
            continue
        ans += [file[file.find('final-result-') + len('final-result-'):file.find('.rs')]]
print(ans)