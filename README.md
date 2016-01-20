Synthesizing Correct-by-Construction Assembly for Cryptographic Primitives
-----

... which would make a good paper title.

To build:

	git clone git@github.mit.edu:plv/bedrock.git
	( cd bedrock && make Bedrock/Word.vo )
	( cd coqprime && make PrimalityTest/Zp.vo PrimalityTest/PocklingtonCertificat.vo )
	make
