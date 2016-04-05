We use SatAbs as the predicate abstraction engine to construct Boolean programs and 
thread-state transition system (TTS). You can download SatAbs here:

   http://www.cprover.org/satabs/

1. To generate Boolean programs, you can use the following command: 

   satabs -DSATABS --concurrency --full-inlining  --save-bps <input-file>

2. To generate TTS, you can use above command with option "--build-tts".
