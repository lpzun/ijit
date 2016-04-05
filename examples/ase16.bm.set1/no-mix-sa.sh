rm -rf *.tts
rm -rf *.bp
exec satabs -DSATABS --concurrency --save-bps --no-mixed-predicates $@ --max-threads 5
