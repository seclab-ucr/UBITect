#!/bin/bash
python main.py json0-1.json
ret=$?

echo "Got SIGNAL $sig" >> ./log.log
#
#  returns > 127 are a SIGNAL
#
if [ $ret -gt 127 ]; then
        sig=$((ret - 128))
        if [ $sig -eq $(kill -l SIGKILL) ]; then
                echo "process was killed with SIGKILL" >> ./log.log
                dmesg >> ./log.log
        fi
fi
