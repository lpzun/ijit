#exec find . -name '*.bp' | xargs grep -H '\$'
exec ls | egrep "*.tts" | xargs grep -H '+>'
