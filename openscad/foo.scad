$fn = 48;
if ($t >= 0.0 && $t < 0.025){   
	difference(){
		union() {
			translate(v = [0.,0.,0.]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.,0.,0.]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.,-0.,-0.]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.,0.,0.]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.,-0.,-0.]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.,-0.,-0.]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.,0.,0.]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.,0.,0.]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.,-0.,-0.]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.,0.,0.]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.,-0.,-0.]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.,-0.,-0.]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.,0.,0.]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.025 && $t < 0.05){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.09995834]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.09995834,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.14993751]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.14993751]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.09995834,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.14993751]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.14993751]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.09995834,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.14993751]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.14993751]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.09995834,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.14993751]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.14993751]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.05 && $t < 0.075){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.19966683]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.19966683,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.29950025]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.29950025]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.19966683,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.29950025]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.29950025]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.19966683,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.29950025]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.29950025]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.19966683,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.29950025]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.29950025]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.075 && $t < 0.1){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.29887626]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.29887626,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-0.4483144]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,0.4483144]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.29887626,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-0.4483144]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,0.4483144]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.29887626,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-0.4483144]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,0.4483144]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.29887626,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-0.4483144]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,0.4483144]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.1 && $t < 0.125){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.39733866]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.39733866,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.59600799]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.59600799]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.39733866,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.59600799]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.59600799]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.39733866,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.59600799]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.59600799]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.39733866,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.59600799]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.59600799]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.125 && $t < 0.15){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.49480792]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.49480792,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.74221188]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.74221188]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.49480792,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.74221188]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.74221188]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.49480792,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.74221188]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.74221188]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.49480792,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.74221188]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.74221188]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.15 && $t < 0.175){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.59104041]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.59104041,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.88656062]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.88656062]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.59104041,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.88656062]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.88656062]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.59104041,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.88656062]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.88656062]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.59104041,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.88656062]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.88656062]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.175 && $t < 0.2){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.68579561]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.68579561,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.02869342]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.02869342]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.68579561,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.02869342]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.02869342]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.68579561,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.02869342]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.02869342]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.68579561,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.02869342]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.02869342]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.2 && $t < 0.225){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.77883668]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.77883668,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.16825503]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.16825503]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.77883668,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.16825503]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.16825503]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.77883668,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.16825503]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.16825503]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.77883668,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.16825503]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.16825503]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.225 && $t < 0.25){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.86993107]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.86993107,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-1.3048966]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,1.3048966]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.86993107,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-1.3048966]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,1.3048966]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.86993107,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-1.3048966]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,1.3048966]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.86993107,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-1.3048966]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,1.3048966]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.25 && $t < 0.275){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.95885108]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.95885108,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.43827662]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.43827662]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.95885108,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.43827662]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.43827662]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.95885108,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.43827662]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.43827662]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.95885108,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.43827662]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.43827662]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.275 && $t < 0.3){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.04537446]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.04537446,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.56806169]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.56806169]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.04537446,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.56806169]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.56806169]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.04537446,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.56806169]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.56806169]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.04537446,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.56806169]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.56806169]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.3 && $t < 0.325){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.12928495]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.12928495,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.69392742]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.69392742]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.12928495,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.69392742]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.69392742]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.12928495,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.69392742]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.69392742]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.12928495,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.69392742]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.69392742]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.325 && $t < 0.35){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.21037281]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.21037281,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.81555922]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.81555922]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.21037281,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.81555922]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.81555922]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.21037281,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.81555922]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.81555922]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.21037281,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.81555922]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.81555922]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.35 && $t < 0.375){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.28843537]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.28843537,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.93265306]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.93265306]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.28843537,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.93265306]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.93265306]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.28843537,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.93265306]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.93265306]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.28843537,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.93265306]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.93265306]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.375 && $t < 0.4){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.36327752]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.36327752,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.04491628]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.04491628]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.36327752,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.04491628]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.04491628]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.36327752,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.04491628]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.04491628]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.36327752,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.04491628]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.04491628]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.4 && $t < 0.425){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.43471218]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.43471218,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.15206827]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.15206827]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.43471218,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.15206827]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.15206827]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.43471218,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.15206827]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.15206827]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.43471218,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.15206827]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.15206827]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.425 && $t < 0.45){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.50256081]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.50256081,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.25384122]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.25384122]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.50256081,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.25384122]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.25384122]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.50256081,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.25384122]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.25384122]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.50256081,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.25384122]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.25384122]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.45 && $t < 0.475){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.56665382]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.56665382,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.34998073]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.34998073]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.56665382,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.34998073]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.34998073]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.56665382,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.34998073]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.34998073]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.56665382,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.34998073]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.34998073]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.475 && $t < 0.5){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.62683101]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.62683101,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.44024651]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.44024651]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.62683101,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.44024651]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.44024651]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.62683101,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.44024651]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.44024651]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.62683101,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.44024651]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.44024651]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.5 && $t < 0.525){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.68294197]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.68294197,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.52441295]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.52441295]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.68294197,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.52441295]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.52441295]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.68294197,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.52441295]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.52441295]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.68294197,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.52441295]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.52441295]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.525 && $t < 0.55){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.62683101]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.62683101,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.44024651]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.44024651]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.62683101,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.44024651]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.44024651]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.62683101,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.44024651]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.44024651]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.62683101,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.44024651]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.44024651]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.55 && $t < 0.575){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.56665382]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.56665382,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.34998073]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.34998073]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.56665382,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.34998073]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.34998073]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.56665382,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.34998073]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.34998073]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.56665382,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.34998073]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.34998073]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.575 && $t < 0.6){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.50256081]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.50256081,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.25384122]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.25384122]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.50256081,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.25384122]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.25384122]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.50256081,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.25384122]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.25384122]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.50256081,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.25384122]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.25384122]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.6 && $t < 0.625){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.43471218]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.43471218,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.15206827]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.15206827]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.43471218,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.15206827]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.15206827]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.43471218,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.15206827]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.15206827]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.43471218,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.15206827]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.15206827]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.625 && $t < 0.65){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.36327752]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.36327752,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.04491628]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.04491628]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.36327752,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-2.04491628]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,2.04491628]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.36327752,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.04491628]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.04491628]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.36327752,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-2.04491628]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,2.04491628]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.65 && $t < 0.675){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.28843537]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.28843537,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.93265306]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.93265306]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.28843537,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.93265306]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.93265306]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.28843537,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.93265306]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.93265306]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.28843537,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.93265306]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.93265306]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.675 && $t < 0.7){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.21037281]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.21037281,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.81555922]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.81555922]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.21037281,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.81555922]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.81555922]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.21037281,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.81555922]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.81555922]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.21037281,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.81555922]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.81555922]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.7 && $t < 0.725){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.12928495]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.12928495,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.69392742]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.69392742]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.12928495,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.69392742]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.69392742]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.12928495,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.69392742]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.69392742]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.12928495,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.69392742]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.69392742]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.725 && $t < 0.75){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,1.04537446]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [1.04537446,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.56806169]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.56806169]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.04537446,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.56806169]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.56806169]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [1.04537446,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.56806169]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.56806169]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-1.04537446,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.56806169]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.56806169]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.75 && $t < 0.775){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.95885108]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.95885108,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.43827662]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.43827662]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.95885108,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.43827662]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.43827662]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.95885108,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.43827662]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.43827662]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.95885108,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.43827662]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.43827662]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.775 && $t < 0.8){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.86993107]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.86993107,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-1.3048966]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,1.3048966]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.86993107,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-1.3048966]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,1.3048966]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.86993107,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-1.3048966]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,1.3048966]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.86993107,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-1.3048966]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,1.3048966]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.8 && $t < 0.825){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.77883668]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.77883668,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.16825503]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.16825503]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.77883668,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.16825503]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.16825503]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.77883668,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.16825503]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.16825503]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.77883668,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.16825503]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.16825503]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.825 && $t < 0.85){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.68579561]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.68579561,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.02869342]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.02869342]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.68579561,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-1.02869342]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,1.02869342]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.68579561,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.02869342]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.02869342]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.68579561,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-1.02869342]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,1.02869342]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.85 && $t < 0.875){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.59104041]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.59104041,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.88656062]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.88656062]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.59104041,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.88656062]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.88656062]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.59104041,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.88656062]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.88656062]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.59104041,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.88656062]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.88656062]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.875 && $t < 0.9){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.49480792]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.49480792,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.74221188]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.74221188]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.49480792,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.74221188]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.74221188]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.49480792,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.74221188]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.74221188]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.49480792,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.74221188]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.74221188]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.9 && $t < 0.925){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.39733866]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.39733866,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.59600799]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.59600799]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.39733866,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.59600799]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.59600799]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.39733866,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.59600799]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.59600799]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.39733866,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.59600799]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.59600799]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.925 && $t < 0.95){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.29887626]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.29887626,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-0.4483144]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,0.4483144]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.29887626,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.       ,-0.       ,-0.4483144]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.       ,0.       ,0.4483144]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.29887626,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-0.4483144]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,0.4483144]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.29887626,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.       ,-0.       ,-0.4483144]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.       ,0.       ,0.4483144]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.95 && $t < 0.975){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.19966683]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.19966683,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.29950025]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.29950025]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.19966683,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.29950025]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.29950025]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.19966683,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.29950025]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.29950025]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.19966683,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.29950025]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.29950025]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
if ($t >= 0.975 && $t < 1.0){   
	difference(){
		union() {
			translate(v = [0.        ,0.        ,0.09995834]) {
				translate(v = [-5.0000000000, -1.2500000000, -1.2500000000]) {
					cube(size = [10, 2.5000000000, 2.5000000000]);
				}
			}
			translate(v = [0.09995834,0.        ,0.        ]) {
				translate(v = [-4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.14993751]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.14993751]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.09995834,-0.        ,-0.        ]) {
				translate(v = [4.5000000000, 0, 0]) {
					translate(v = [0, -2.5000000000, 0]) {
						rotate(a = [0, 90, 90]) {
							union() {
								translate(v = [-0.        ,-0.        ,-0.14993751]) {
									difference() {
										color(c = [1, 0, 0]) {
											cylinder(h = 0.5000000000, r = 2);
										}
									}
								}
								color(c = [0, 0, 1]) {
									cylinder(h = 5, r = 0.2500000000);
								}
								translate(v = [0.        ,0.        ,0.14993751]) {
									translate(v = [0, 0, 4.5000000000]) {
										difference() {
											color(c = [1, 0, 0]) {
												cylinder(h = 0.5000000000, r = 2);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		/* Holes Below*/
		union(){
			translate(v = [0.09995834,0.        ,0.        ]){
				translate(v = [-4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.14993751]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.14993751]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
			translate(v = [-0.09995834,-0.        ,-0.        ]){
				translate(v = [4.5000000000, 0, 0]){
					translate(v = [0, -2.5000000000, 0]){
						rotate(a = [0, 90, 90]){
							union(){
								translate(v = [-0.        ,-0.        ,-0.14993751]){
									union(){
										color(c = [0, 0, 1]) {
											cylinder(h = 5, r = 0.2500000000);
										}
									}
								}
								translate(v = [0.        ,0.        ,0.14993751]){
									translate(v = [0, 0, 4.5000000000]){
										union(){
											color(c = [0, 0, 1]) {
												cylinder(h = 5, r = 0.2500000000);
											}
										}
									}
								}
							}
						}
					}
				}
			}
		} /* End Holes */ 
	}
}
