#!/bin/bash
RED='\033[0;31m'
NC='\033[0m'  
rm -rf transcript 

if ./compile.sh
then
	echo "Success"
else
	echo "Failure"
	exit 1
fi

printf "${RED}\nSimulating${NC}\n"
if [[ "$@" =~ --gui ]]
then
  	echo vsim -assertdebug -voptargs="+acc" test_hdlc bind_hdlc -do "log -r *" &
  	exit
else
	if vsim -assertdebug -c -voptargs="+acc" test_hdlc bind_hdlc -do "log -r *; run -all; exit" 
	then
		echo "Success"
	else
		echo "Failure"
		exit 1
	fi
fi
