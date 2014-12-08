Netcow
======

NETwork COnfiguration Verification and Validation



In the context of this project, terms Validation and Verification have the following meaning:
* Validation is process to assure that configuration obey schema and predefined general rules. 
* Verification is the evaluation whether a configuration complies with policy requirements and specification. 



This idea of this project is to create couple of domain models for network configuration, policy, routing and reachability. These domains are modeled using Microsoft's Formula, which enables to generate domain object definitions in terms of C# classes. To automate the process, generators and transformers are provided as F# tools. These tools take input models and generate output models for further analysis.   

There are following domains of models:
* Network Domain
* Policy Domain
* Firewall Domain
* Routing Domain
* Reachability
These domains specify structure and rules for particular sets of models. Network Models and Policy models are generated from input files, which are, respectively, network configuration files and policy specification files.  

Domains 
=======

Network domain
--------------


Policy domain
-------------

Firewall domain
---------------

Routing domain
--------------

Reachability domain
-------------------

Validation
==========


Verification
============
