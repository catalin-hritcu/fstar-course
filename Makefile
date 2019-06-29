
verify:
	make -C code/pure-fun
	make -C code/state
	make -C code/monotonic
#	make -C code/effects
	make -C ex
	make -C sol

clean:
	make -C code/pure-fun clean
	make -C code/state clean
	make -C code/monotonic clean
#	make -C code/effects
	make -C ex clean
	make -C sol clean

dist:
	make -C slides
	rsync -av --progress . /home/hritcu/Inria/www-hritcu/teaching/vtsa2019 --exclude '*.exe' --exclude 'code' --exclude 'ex' --exclude 'sol' --exclude 'Makefile*' --exclude '*~'
	cd /home/hritcu/Inria/www-hritcu; make
