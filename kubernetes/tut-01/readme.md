# K8s Tut 01

## Source

https://auth0.com/blog/kubernetes-tutorial-step-by-step-introduction-to-basic-concepts/

## Version

    $ kubectl version
    Client Version: version.Info{Major:"1", Minor:"14", GitVersion:"v1.14.1", GitCommit:"b7394102d6ef778017f2ca4046abbaa23b88c290", GitTreeState:"clean", BuildDate:"2019-04-08T17:11:31Z", GoVersion:"go1.12.1", Compiler:"gc", Platform:"linux/amd64"}
    Server Version: version.Info{Major:"1", Minor:"14", GitVersion:"v1.14.1", GitCommit:"b7394102d6ef778017f2ca4046abbaa23b88c290", GitTreeState:"clean", BuildDate:"2019-04-08T17:02:58Z", GoVersion:"go1.12.1", Compiler:"gc", Platform:"linux/amd64"}

## Commands

### Run Tutorial

    $ ./create.sh

## Play around wih the tutorial

    $ kubectl get svc \
    -n ingress-nginx ingress-nginx \
    -o=jsonpath='{.status.loadBalancer.ingress[0].ip}'

Point browser at the IP address returned...


## Cleanup Tutorial

    $ ./teardown.sh

## Files

* cloud-generic.yaml
* create.md
* deployment.yaml
* ingress.yaml
* mandatory.yaml
* service.yaml

## Relationships

cloud-generic.yaml
deployment.yaml
ingress.yaml
mandatory.yaml
service.yaml




