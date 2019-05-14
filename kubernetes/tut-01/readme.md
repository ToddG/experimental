# K8s Tut 01

## Source

https://auth0.com/blog/kubernetes-tutorial-step-by-step-introduction-to-basic-concepts/

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




