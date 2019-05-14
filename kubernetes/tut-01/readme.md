# Tutorial

### Link: https://auth0.com/blog/kubernetes-tutorial-step-by-step-introduction-to-basic-concepts/

## Create

### Create dir

    $ mkdir k8s-tutorial
    $ cd k8s-tutorial/

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services

### Create deployment

A deployment.yaml specifies the containers : [{name,image,port}]. After running we should see pods (containers) created.

    $ kubectl apply -f deployment.yaml

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services

### Download and apply ingress controller 1/2

Metric-ton of configuration for Nginx...

Note, I already did this and added to this repo.

    curl https://raw.githubusercontent.com/kubernetes/ingress-nginx/master/deploy/mandatory.yaml -o mandatory.yaml

On with the show...

    $ kubectl apply -f mandatory.yaml

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get nodes -n ingress-nginx


### Download and apply ingress controller 2/2

Specifies a service? : [port,port,...]

Note, I already did this and added to this repo.

    curl https://raw.githubusercontent.com/kubernetes/ingress-nginx/master/deploy/provider/cloud-generic.yaml -o cloud-generic.yaml

On with the show...

    $ kubectl apply -f cloud-generic.yaml

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get nodes -n ingress-nginx

### Expose deployment port via ClusterIP service

Specifies a port redirect from 80 to 3000 for selector -> '...-deployment'

    $ kubectl apply -f service.yaml

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get nodes -n ingress-nginx

### Define service ingress

    $ kubectl apply -f ingress.yaml
    $ kubectl get svc -n ingress-nginx ingress-nginx -o=jsonpath='{.status.loadBalancer.ingress[0].ip}'
    $ curl (kubectl get svc -n ingress-nginx ingress-nginx -o=jsonpath='{.status.loadBalancer.ingress[0].ip}')


## Destroy

    _DESTROY_ ...
